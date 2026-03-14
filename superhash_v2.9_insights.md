# Insights: SuperHash v2.9 — TrustHash Full Pipeline + Crypto Rules in Saturation

**Fecha**: 2026-03-14
**Dominio**: lean4
**Estado**: v2.8 complete (58 jobs, 0 sorry, 681 thms, Boura-Canteaut integrated)

---

## 1. Resumen Ejecutivo

v2.9 cierra los dos gaps más significativos entre SuperHash y superhash_idea.md:
- **Task A**: TrustHash full fitness pipeline (DP sobre tree decompositions)
- **Task B**: Reglas crypto REALES en el saturation loop (no rules := [])

---

## 2. Hallazgo Clave #1: TrustHash Pipeline — Solo 34 archivos necesarios (18%)

### Minimum Viable Pipeline: 6.2K LOC de 34K totales

La auditoría exhaustiva de TrustHash identificó 5 tiers de dependencias sin ciclos:

| Tier | Archivos | LOC | Contenido |
|------|----------|-----|-----------|
| **T1: Verdict** | 4 | 701 | PipelineVerdict, StructuralPipeline, GenericFloorPipeline, WideTrailPipeline |
| **T2: DP Chain** | 5 | 883 | SecurityDP, CryptoCost, NiceTree, DPBridge, DPOperations |
| **T3: Graph/Tree** | 6 | 733 | TreeDecomp, NiceTreeConvert, Graph, EliminationOrder, TrailBridge, TWBridge |
| **T4: S-box Compute** | 5 | 599 | DDTCompute, LATCompute, AlgDegreeCompute, SboxBridge, SboxTable |
| **T5: Support** | 14 | 2,100 | HashSpec, CostModel, FullVerdict, ModeAnalysis, ComputeInstances, etc. |
| **Total** | **34** | **~6.2K** | **18% de TrustHash** |

**El 82% restante NO se necesita** (E-graph propio de TrustHash, modelos de ataques específicos, cifrados concretos).

### Dependency DAG (sin ciclos — safe to copy layer by layer)

```
Layer 0: Bitwise, CostModel, FinIter, FullVerdict, Graph, ModeAnalysis (leaves)
Layer 1: DegreeFold, DiffTrail, EliminationOrder, RoundStructure, FoldCostBound
Layer 2: Sbox.DDTCompute, Sbox.LATCompute, Sbox.AlgDegreeCompute, Sbox.SboxBridge, Sbox.SboxTable
Layer 3: HashSpec
Layer 4: TreeDecomp, NiceTreeConvert, TWBridge, TrailBridge
Layer 5: DP.NiceTree, DP.DPOperations, DP.CryptoCost, DP.DPBridge, DP.SecurityDP
Layer 6: Pipeline.GenericFloorPipeline, Pipeline.StructuralPipeline, Pipeline.WideTrailPipeline, Pipeline.PipelineVerdict
```

### Verdict Entry Point

**Archivo**: `TrustHash/Pipeline/PipelineVerdict.lean` (190 LOC)
```lean
def computeVerdict (s : HashSpec) : Nat :=
  min (computeGenericFloor s) (computeStructCost s)
```

**Fórmula completa**:
```
verdict = min(genericFloor, min(δ^activeSboxes, degree^treewidth))
```

### API Compatibility (Lean 4.16 → 4.28)

- **L-489 confirma**: HashMap Std API idéntica entre versiones
- **Nat.pos_pow_of_pos**: renombrado en 4.28 (fix con shim de 3 líneas, ya probado en v2.8)
- **omega tactic**: disponible en ambas versiones
- **L-523**: ~1 bug por 700 LOC en adaptaciones — para 6.2K LOC → ~9 bugs esperados (mecánicos)

---

## 3. Hallazgo Clave #2: Reglas Crypto → Saturation — 3 niveles de abstracción

### La torre de reglas en SuperHash

```
Nivel 3: CryptoEquivRule / CryptoImproveRule  (v2.5, Crypto/CryptoRule.lean)
         ↓ NO directamente convertible (crypto-semantic domain)
Nivel 2: PatternSoundRule CryptoOp Val        (v1.0+, Pipeline/EMatchSpec.lean)
         ↓ .rule field → RewriteRule
Nivel 1: RewriteRule CryptoOp                 (EMatch.lean, syntactic patterns)
         ↓
         saturateF (acepta List (RewriteRule CryptoOp))
```

### El gap específico

`saturateF` acepta `List (RewriteRule Op)` — patrones sintácticos para e-matching.

Las 5 reglas crypto v2.5 (`sbox_substitute_degree`, `sbox_compose_assoc`, etc.) son `CryptoEquivRule` que operan sobre `CryptoOp → CryptoSemantics`. **No son PatternSoundRule** — no tienen Pattern LHS/RHS ni e-matching.

### Pero: Las 5 reglas v1.0 YA SON PatternSoundRule

`Rules/CryptoRules.lean:231-306` tiene 5 instancias listas:
```lean
def cryptoPatternRules : List (PatternSoundRule CryptoOp Nat) :=
  [iterateOne_psound, parallelIdentity_psound, composeAssoc_psound,
   roundCompose_psound 7 5, iterateCompose_psound 10 2]
```

Estas YA tienen `.rule : RewriteRule CryptoOp` y pueden pasarse directamente a `saturateF`.

### Solución pragmática (2 fases)

**Fase A (inmediata)**: Usar las 5 reglas v1.0 existentes (`PatternSoundRule CryptoOp Nat`) en `designLoopStep`. Solo cambiar `rules := []` → `rules := (cryptoPatternRules.map (·.rule))`.

**Fase B (posterior)**: Crear converter `CryptoEquivRule.toPatternSoundRule` para elevar las 5 reglas crypto v2.5 a PatternSoundRule format. Requiere:
1. Pattern constructors para cada CryptoOp
2. Proof bridge: `Pattern.eval` ↔ `evalCryptoSem`
3. `AllDistinctChildren` proofs

### Cambio exacto en designLoopStep

```lean
-- ANTES (v2.7):
let satRules : List (RewriteRule CryptoOp) := []

-- DESPUÉS (v2.9 Fase A):
let satRules : List (RewriteRule CryptoOp) :=
  cryptoPatternRules.map (·.rule)
```

**3 líneas de cambio** para activar la saturación con reglas reales.

---

## 4. Hallazgo Clave #3: El pipeline DP de TrustHash es autónomo

### SecurityDP: el core del fitness

`TrustHash/DP/SecurityDP.lean` (158 LOC) computa:
```lean
securityDP(δ, d, tree) = min(differentialDP, algebraicDP)
```

Donde:
- `differentialDP` = DP bottom-up sobre nice tree con costo δ^{activeSboxes por bag}
- `algebraicDP` = DP bottom-up sobre nice tree con costo degree^{treewidth}

### NiceTree: 4-constructor inductive

```lean
inductive NiceNode where
  | leaf (bag : List Nat)
  | introduce (vertex : Nat) (child : NiceNode)
  | forget (vertex : Nat) (child : NiceNode)
  | join (left right : NiceNode)
```

SuperHash ya tiene `DynamicTreeProg` (122 thms) en la librería interna con una estructura similar. Los DP operations (`dpLeaf`, `dpIntroduce`, `dpForget`, `dpJoin`) son patterns conocidos.

### Constraint Graph → Tree Decomposition

`TrustHash/TreeDecomp.lean` (138 LOC) + `EliminationOrder.lean` (92 LOC):
- Input: `SimpleGraph` (vertices = variables, edges = dependencies)
- Algorithm: greedy min-degree elimination
- Output: tree decomposition → nice tree conversion

**Workaround para v2.9**: En lugar de copiar el constraint graph completo, usar `ComputeInstances` que hardcodea nice trees para AES/Poseidon. Esto da verdicts concretos sin el pipeline de generación automática de grafos.

---

## 5. Estrategia de Implementación

### Approach: Bottom-up layer copy + immediate saturation fix

**Semana 1 (1-2 días)**: Task B — Activar saturation con reglas
1. Cambiar `designLoopStep` de `rules := []` a `rules := cryptoPatternRules.map (·.rule)` (3 líneas)
2. Agregar `import SuperHash.Rules.CryptoRules` a DesignLoop/Core.lean
3. Verificar que saturación produce output.length > 1 con reglas activas
4. Non-vacuity: `example` mostrando diseño alternativo descubierto por saturación

**Semana 1-2 (3-5 días)**: Task A — TrustHash fitness pipeline
1. **Layer 0-1**: Copiar leaf modules (Bitwise, CostModel, Graph, etc.) — ~800 LOC
2. **Layer 2**: Copiar S-box compute chain — ~600 LOC (DDT/LAT ya existen parcialmente en SuperHash)
3. **Layer 3-4**: Copiar HashSpec + Tree decomposition — ~500 LOC
4. **Layer 5**: Copiar DP chain — ~900 LOC (mayor complejidad)
5. **Layer 6**: Copiar Pipeline verdict — ~700 LOC
6. Namespace: `TrustHash.X` → `SuperHash.TrustHash.X`
7. Fix shim: `Nat.pos_pow_of_pos` → compatibility (ya probado en v2.8)
8. Build + test con AES/Poseidon verdicts

---

## 6. Código Reutilizable

### De TrustHash (copiar)
| Path | LOC | Propósito |
|------|-----|-----------|
| `Pipeline/PipelineVerdict.lean` | 190 | Entry point: `computeVerdict` |
| `Pipeline/StructuralPipeline.lean` | 150 | Structural cost computation |
| `Pipeline/GenericFloorPipeline.lean` | 168 | Birthday/GBP/Joux floor |
| `DP/SecurityDP.lean` | 158 | Core DP security computation |
| `DP/NiceTree.lean` | 213 | Nice tree inductive + runDP |
| `DP/DPOperations.lean` | 216 | leaf/introduce/forget/join |
| `TreeDecomp.lean` | 138 | Tree decomposition |
| `NiceTreeConvert.lean` | 120 | Standard form conversion |

### De SuperHash (ya existe, reutilizar)
| Path | Qué tiene | Uso |
|------|-----------|-----|
| `Rules/CryptoRules.lean:231-306` | 5 PatternSoundRule instances | Pasar a saturateF directamente |
| `Pipeline/Saturate.lean:358` | saturateF definition | Acepta List RewriteRule |
| `Pipeline/CompletenessSpec.lean` | extractAuto_complete | Extraction siempre produce resultado |
| `Crypto/CryptoNodeSemantics.lean` | NodeSemantics CryptoSemantics | Pipeline sobre crypto real |

---

## 7. Lecciones Aplicables

| ID | Título | Aplicación |
|----|--------|-----------|
| **L-523** | Library adaptation (~1 bug/700 LOC) | TrustHash copy: ~9 bugs en 6.2K LOC |
| **L-489** | HashMap API stable 4.16→4.28 | Sin cambios breaking |
| **L-336** | Bridge con wrapper isomorphisms | HashSpec → SuperHash types |
| **L-518** | ClassNodesSemantic boundary | BestNodeInv interface para DP |
| **L-513** | Compositional E2E proofs | Pipeline verdict composition |
| **L-544** | K_n constraint graph modeling | Treewidth analysis of SPN |

---

## 8. Riesgos

| Riesgo | Nivel | Mitigación |
|--------|-------|-----------|
| 34 archivos TrustHash con import rewires | MEDIO | Copy layer-by-layer (DAG sin ciclos) |
| Nat.pos_pow_of_pos en TrustHash code | BAJO | Shim de 3 líneas (ya probado en v2.8) |
| HashSpec types ≠ SuperHash CryptoSemantics | MEDIO | Bridge adapter (~100 LOC) |
| saturateF con reglas produce e-graph grande | BAJO | Fuel limit ya existe (parameter) |
| DP operations timeout en large trees | BAJO | TrustHash tiene concrete instances |
| CryptoEquivRule → PatternSoundRule bridge | ALTO | Defer a Fase B; usar v1.0 rules primero |

---

## 9. Estimación

| Task | LOC | Esfuerzo | Impacto |
|------|-----|----------|---------|
| B: Activar saturación con reglas | ~20 | 30 min | **ALTO** (turn the key) |
| A Layer 0-1: Leaf modules | ~800 | 1-2h | Foundation |
| A Layer 2: S-box compute | ~600 | 1-2h | DDT/LAT pipeline |
| A Layer 3-4: Tree decomposition | ~500 | 1-2h | Structural analysis |
| A Layer 5: DP chain | ~900 | 2-3h | Core security DP |
| A Layer 6: Pipeline verdict | ~700 | 1-2h | Final verdict |
| A Integration tests | ~200 | 1h | Non-vacuity + smoke |
| **Total** | **~3,720** | **~2-3 días** | |

---

## 10. Orden de Ejecución Recomendado

1. **Task B primero** (30 min, max impacto): cambiar `rules := []` → `cryptoPatternRules.map (·.rule)`. Esto activa la saturación con reglas REALES por primera vez. Verificar que produce diseños alternativos.

2. **Task A layers 0-4** (1 día): copiar foundation + tree decomposition de TrustHash. Build incremental por layer.

3. **Task A layers 5-6** (1 día): copiar DP + verdict pipeline. Conectar con SuperHash types.

4. **Integration** (medio día): smoke tests con AES/Poseidon verdicts. Comparar con `computeVerdict` existente (v2.8 approximation) vs TrustHash real.

**Resultado final**: SuperHash con equality saturation ACTIVA (reglas reales) + TrustHash fitness COMPLETO (DP-based verdicts). Esto cubre ~90% de superhash_idea.md.
