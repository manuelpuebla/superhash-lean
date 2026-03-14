# Insights: SuperHash v2.8 — OptiSat Completeness + TrustHash Fitness + Boura-Canteaut Integration

**Fecha**: 2026-03-14
**Dominio**: lean4
**Estado del objeto**: upgrade (v2.7 complete: 53 jobs, 0 sorry, NodeSemantics CryptoSemantics instance)
**Profundidad**: standard (3 agentes paralelos, bibliotecas internas + online)

---

## 1. Estado Actual del Proyecto

SuperHash v2.7 tiene:
- **53 build jobs, ZERO sorry**
- `instance : NodeSemantics CryptoOp CryptoSemantics` (v2.7 T3)
- AES S-box DDT certificada (v2.7 T2)
- Pipeline infrastructure **parametric** over `[NodeSemantics Op Val]`
- `superhash_pipeline_correct` **hardcoded a Nat** (único bottleneck)

Tres tareas pendientes: OptiSat completeness (T4), TrustHash fitness (T5), Boura-Canteaut (T6).

---

## 2. Hallazgo Clave #1: El pipeline es 95% parametric

### Lo que YA funciona para CryptoSemantics (sin cambios):
| Componente | Estado | Archivo |
|-----------|--------|---------|
| `NodeSemantics CryptoOp CryptoSemantics` | ✓ Instance | CryptoNodeSemantics.lean |
| `ConsistentValuation` para CryptoSemantics | ✓ Compila | (parametric via typeclass) |
| `saturateF_preserves_consistent_internal` | ✓ Polymorphic | EMatchSpec.lean:1098 |
| `optimizeF_soundness` | ✓ Polymorphic | Soundness.lean:146 |
| `sameShapeSemantics_holds` | ✓ Auto-proved | EMatchSpec.lean:70 |
| `InstantiateEvalSound_holds` | ✓ Generic | EMatchSpec.lean:675 |
| `extractF_correct` | ✓ Polymorphic | Extract.lean:200 |

### Lo que está hardcoded a Nat:
| Componente | Problema | Archivo |
|-----------|----------|---------|
| `superhash_pipeline_correct` | `Val := Nat` explícito | Integration.lean:56 |
| `pipeline_soundness` | `Val := Nat` explícito | MasterTheorem.lean:35 |
| `crypto_extractable_sound` | `ExtractableSound CryptoOp CryptoExpr Nat` | Instances.lean:48 |

### Insight: El bottleneck es `ExtractableSound`

`CryptoExpr.eval` retorna **Nat** (metrics como números), no `CryptoSemantics`. Esto significa que la extracción siempre produce diseños Nat-valued. El pipeline CryptoSemantics opera así:

```
Saturation: Val := CryptoSemantics (intermediate, para razonamiento)
Extraction: Val := Nat (final, porque CryptoExpr.eval → Nat)
Bridge:     projectToNat : CryptoSemantics → Nat
```

**Implicación para T4**: No necesitamos `ExtractableSound CryptoOp CryptoExpr CryptoSemantics`. Necesitamos una **composición**: saturar en CryptoSemantics, luego extraer en Nat, con un bridge theorem que conecte ambos.

---

## 3. Hallazgo Clave #2: OptiSat Completeness Gaps

### Qué YA tiene SuperHash (copiado de OptiSat):
- `extractF`, `extractAuto`, `extractF_correct`, `extractAuto_correct`
- `computeCostsF_preserves_consistency`, `computeCostsF_bestNode_in_nodes`
- `rebuildF_preserves_pmi`, `bestNodeInv_empty`, `add_preserves_bestNodeInv`

### Qué FALTA (OptiSat tiene pero SuperHash no):
| Theorem | OptiSat File:Lines | Propósito |
|---------|-------------------|-----------|
| `BestNodeChild` | CompletenessSpec:44-49 | Definición de arista en DAG de bestNode |
| `AcyclicBestNodeDAG` | CompletenessSpec:52-56 | Existencia de ranking → DAG |
| `BestCostLowerBound` | CompletenessSpec:60-69 | Invariante self-referencial de costo |
| `bestCostLowerBound_acyclic` | CompletenessSpec:100-117 | **G1**: LB + costos positivos → acíclico |
| `computeCostsF_bestCost_lower_bound` | CompletenessSpec:315-326 | Cómputo preserva LB |
| `computeCostsF_acyclic` | CompletenessSpec:330-341 | **Cómputo produce DAG** |
| `extractF_of_rank` | CompletenessSpec:364-403 | **G2**: ranking + fuel → extracción exitosa |
| `extractAuto_complete` | CompletenessSpec:409-424 | **Fuel sufficiency**: extractAuto siempre produce resultado |

**Estos son "completeness gap closers" — prueban que la extracción SIEMPRE produce un resultado dado fuel suficiente.** SuperHash v1.0 solo probó correctness (el resultado es semánticamente correcto), no completeness (siempre hay resultado).

**Estos theorems son genéricos sobre `Op` y `Expr`** — se instancian automáticamente para CryptoOp.

---

## 4. Hallazgo Clave #3: TrustHash Bridge Architecture

### HashOp vs CryptoOp Mapping

| CryptoOp (12) | HashOp (11+2) | Mapping |
|---------------|---------------|---------|
| `sbox d c` | `sboxApply c d` | Directo (args invertidos) |
| `linear bn c` | `mdsMix [c] bn` | List wrapper |
| `xor l r` | `addRoundKey l r` | Directo |
| `round d bn c` | `roundFunc c 1` | + metadata |
| `compose f s` | `compose f s` | Idéntico |
| `iterate n b` | `roundFunc b n` | Nombre diferente |
| `const v` | `constOp v` | Nombre diferente |
| `spnBlock r s l` | (no equiv) | Decompose |
| `feistelBlock r f` | (no equiv) | Decompose |
| `spongeBlock rt cap p` | (no equiv) | Decompose |
| `arxBlock r a rot x` | (no equiv) | Decompose |
| — | `keccakChi lanes` | No equiv en CryptoOp |
| — | `keccakTheta lanes` | No equiv en CryptoOp |

**Estrategia recomendada**: Option (b) — funciones de traducción con proofs de preservación. ~200 LOC para el bridge.

### Lean 4.16 → 4.28 Compatibility

**L-489 confirma**: HashMap Std API idéntica entre v4.16 y v4.26+. Sin cambios breaking.
**L-523 confirma**: Adaptación de ~700 LOC produce ~1 bug (lambda shadowing).

**Riesgo BAJO** para migration. Las reglas TrustHash compilan unchanged en 4.28.

---

## 5. Hallazgo Clave #4: LeanHash ya tiene 163 theorems de Boura-Canteaut

### Los 3 nuevos módulos (2,425 LOC, 0 sorry):

**BouraCanteutBound.lean** (685 LOC, 55 thms):
- `bcd11Bound(n, degG, gamma)` — **GENERAL** bound, aplica a cualquier SPN
- `bc13Bound(n, degG, invDeg)` — **GENERAL** tighter bound para permutaciones
- `iteratedBcd11(n, degG, gamma, r)` — iterated composition para r rounds
- Monotonicity: `bcd11_mono_degG`, `bcd11_mono_gamma`, `bc13_mono_invDeg`
- **Concreto**: AES (γ=4, 128-bit), Keccak (γ=3, 1600-bit), Poseidon (γ=4)
- 7 non-vacuity examples

**HigherOrderDiff.lean** (711 LOC, 43 thms):
- Higher-order derivatives: `minVanishingDim = deg + 1`
- Attack complexity: `attackQueries = 2^(deg+1)`
- Zero-sum partitions: Keccak-f 24-round size = 2^1590
- Keccak degree tables (fwd: 2→1599, bwd: 3→1599)

**LinearLayerDegree.lean** (1030 LOC, 65 thms):
- `SPNParams` structure with proofs
- Phase transition: `expansionRounds = 1 + natLog(delta, t)`
- `expPhaseBound`, `linPhaseBound`, `combinedBound`
- `Arrangement` classification (strong vs weak)
- Concrete: AES (R_SPN=2), MiMC, Poseidon

**TODOS son Nat-valued y directamente copiables a SuperHash.**

---

## 6. Hallazgo Clave #5: Reed-Muller Bibliography (20 PDFs)

### Top 3 papers para SuperHash:
1. **Boura-Canteaut 2012** (slides, 67pp) — Core BCD11 theorem source
2. **Boura-Canteaut 2011** (inverse degree) — BC13 foundation
3. **Cid-Grassi et al. 2021** — SPN linear layer influence (LinearLayerDegree source)

### Covering radius NO es necesario:
Los 3 módulos LeanHash formalizan los bounds SIN Reed-Muller code theory. Usan:
- Nat arithmetic bounds (BCD11: floor division)
- Iterated composition (recursive application)
- Concrete verification via `native_decide`

**La estrategia alternativa (caso especial bijectivo) YA fue implementada** en BC13 bound.

---

## 7. Lecciones Aplicables

| ID | Título | Aplicación |
|----|--------|-----------|
| **L-523** | Library adaptation pattern (~1 bug/700 LOC) | Copiar TrustHash/OptiSat → SuperHash |
| **L-336** | Bridge architecture con wrapper isomorphisms | HashOp ↔ CryptoOp translation |
| **L-489** | HashMap API stable 4.16→4.28 | No blocking changes for TrustHash migration |
| **L-518** | ClassNodesSemantic as extraction boundary | BestNodeInv interface pattern |
| **L-544** | Treewidth modeling K_n constraint graphs | SPN analysis framework |
| **L-513** | Compositional E2E proofs | Pipeline composition pattern |

---

## 8. Síntesis: Recomendaciones para Plan v2.8

### Task 4 (OptiSat Completeness): PRIORITY HIGH
- **Qué**: Copiar CompletenessSpec.lean de OptiSat (8 definitions/theorems)
- **Por qué**: Completeness proofs están **parametric** — instanciación automática
- **Cómo**: Copy ~300 LOC, adaptar namespaces. L-523: esperar ~0 bugs (idéntico toolchain)
- **Resultado**: `extractAuto_complete` disponible para CryptoOp + `pipeline_soundness_crypto`
- **Esfuerzo**: 2-4 horas

### Task 5 (TrustHash Fitness): PRIORITY MEDIUM
- **Qué**: Bridge HashOp ↔ CryptoOp + copiar fitness pipeline
- **Por qué**: TrustHash tiene el evaluador completo verificado (3546 decls)
- **Cómo**: Option (b) — funciones de traducción (~200 LOC bridge). L-336 pattern.
- **Obstáculo principal**: HashOp tiene Keccak ops (4 constructores) sin equivalente en CryptoOp. Solución: `| keccakChi => default` (unsupported ops retornan trivial)
- **Esfuerzo**: 3-5 días (bulk es mechanical namespace adaptation)

### Task 6 (Boura-Canteaut): **MOSTLY DONE** — just copy
- **Qué**: Copiar los 3 módulos LeanHash (2425 LOC, 163 thms) a SuperHash/Crypto/
- **Por qué**: Ya están formalizados y compilan (0 sorry)
- **Cómo**: Copy/adapt, ajustar imports. NO re-probar.
- **Resultado**: `bcd11Bound`, `bc13Bound`, `iteratedBcd11` disponibles para fitness + rules
- **Esfuerzo**: 1-2 horas (copy + namespace + build)

### Orden de ejecución recomendado:
1. **T6 primero** (copiar LeanHash modules → 1-2h, mayor impacto académico)
2. **T4 después** (copiar OptiSat completeness → 2-4h, cierra pipeline gap)
3. **T5 último** (TrustHash bridge → 3-5 días, mayor esfuerzo)

---

## 9. Riesgos

| Riesgo | Nivel | Mitigación |
|--------|-------|-----------|
| LeanHash 4.16 → SuperHash 4.28 copy issues | BAJO | L-489: API stable. L-523: ~0 bugs |
| OptiSat CompletenessSpec uses definitions not in SuperHash | MEDIO | Copy dependency chain (BestNodeChild → BestCostLowerBound → acyclicity) |
| TrustHash Keccak ops sin equivalente CryptoOp | BAJO | Map to default (unsupported → trivial metrics) |
| `ExtractableSound CryptoSemantics` gap | ALTO | Use composición: saturate in CS, extract in Nat, bridge via projectToNat |
| 163 new theorems create import/namespace conflicts | BAJO | Use `SuperHash.Crypto.BouraCanteutBound` namespace (no conflict) |

---

## 10. Recursos Prioritarios

1. **OptiSat CompletenessSpec.lean** — `/Users/manuelpuebla/Documents/claudio/optisat/LambdaSat/CompletenessSpec.lean`
2. **LeanHash BouraCanteutBound.lean** — `/Users/manuelpuebla/Documents/claudio/leanhash/LeanHash/BouraCanteutBound.lean`
3. **LeanHash HigherOrderDiff.lean** — `/Users/manuelpuebla/Documents/claudio/leanhash/LeanHash/HigherOrderDiff.lean`
4. **LeanHash LinearLayerDegree.lean** — `/Users/manuelpuebla/Documents/claudio/leanhash/LeanHash/LinearLayerDegree.lean`
5. **TrustHash HashOp.lean** — `/Users/manuelpuebla/Documents/claudio/TrustHash/TrustHash/HashOp.lean`
6. **Reed-Muller bibliography** — `~/Documents/claudio/biblioteca/reed-muller/` (20 PDFs indexed)
