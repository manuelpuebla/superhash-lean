# SuperHash v2.9 — ARCHITECTURE

**Proyecto**: SuperHash v2.9
**Base**: v2.8 (58 jobs, 0 sorry, 681 thms, Boura-Canteaut + CompletenessSpec + TrustHash verdict)
**Fuentes**: TrustHash pipeline (34 archivos, ~6.2K LOC), existing PatternSoundRule instances
**Objetivo**: Activar equality saturation con reglas reales + TrustHash DP-based fitness

---

## Visión

v2.9 hace que SuperHash FUNCIONE como lo describe superhash_idea.md:
1. **El E-graph satura con reglas crypto reales** (no rules := [])
2. **TrustHash evalúa diseños via DP sobre tree decompositions** (no approximación)

---

## Fase 1: Activar Saturation con Reglas Reales (Turn the Key)

### N1.1 — Connect Rules to designLoopStep [CRITICO]
- **Archivo**: `SuperHash/DesignLoop/Core.lean` (modificar)
- **Cambio**: Reemplazar `let satRules : List (RewriteRule CryptoOp) := []` con las 5 PatternSoundRule v1.0 existentes
- **Import**: Agregar `import SuperHash.Rules.CryptoRules`
- **Código**:
  ```lean
  let satRules : List (RewriteRule CryptoOp) :=
    cryptoPatternRules.map (·.rule)
  ```
- **Source**: `SuperHash/Rules/CryptoRules.lean:231-306` (5 instancias ya listas)
- **Dificultad**: MUY BAJA (3 líneas de cambio)
- **Impacto**: MÁXIMO — primera vez que equality saturation aplica reglas reales

### N1.2 — Saturation Smoke Test [HOJA]
- **Archivo**: `Tests/NonVacuity/Saturation.lean` (nuevo)
- **Deps**: N1.1
- **Entregables**:
  - `#eval` mostrando que output.length > 1 con reglas activas (diseños alternativos descubiertos)
  - `example` no-vacuity: saturación con regla `iterateOne` transforma `iterate(1, body)` → `body`
  - `example`: saturación con `composeAssoc` reordena composiciones
- **Dificultad**: BAJA

---

## Fase 2: TrustHash DP Pipeline (Copy Layer-by-Layer)

### N2.1 — Foundation Modules (Layers 0-1) [FUNDACIONAL]
- **Archivos**: `SuperHash/TrustHash/Foundations.lean` (nuevo, ~800 LOC)
- **Source**: Copiar/adaptar de TrustHash:
  - `CostModel.lean` (222 LOC) — cost function definitions
  - `Graph.lean` (155 LOC) — SimpleGraph for constraint graphs
  - `ModeAnalysis.lean` (119 LOC) — hash mode (compression, sponge)
  - `RoundStructure.lean` (~100 LOC) — round types (full, partial)
  - `Bitwise.lean`, `FinIter.lean` (~200 LOC) — utility modules
- **Adaptación**: `namespace TrustHash.X` → `namespace SuperHash.TrustHash.X`
- **Dificultad**: BAJA (leaf modules, no deps)

### N2.2 — HashSpec + S-box Chain (Layers 2-3) [FUNDACIONAL]
- **Archivos**: `SuperHash/TrustHash/HashSpec.lean`, `SuperHash/TrustHash/SboxCompute.lean` (nuevos, ~820 LOC)
- **Source**:
  - `HashSpec.lean` (221 LOC) — hash function specification type
  - `Sbox/DDTCompute.lean` (131 LOC) — DDT computation
  - `Sbox/LATCompute.lean` (120 LOC) — LAT computation
  - `Sbox/AlgDegreeCompute.lean` (104 LOC) — algebraic degree
  - `Sbox/SboxBridge.lean` (125 LOC) — S-box → certified params
  - `Sbox/SboxTable.lean` (119 LOC) — S-box lookup tables
- **Nota**: SuperHash ya tiene DDT computation (`Crypto/DDT.lean`) — reutilizar donde posible, bridge donde difiera
- **Dificultad**: BAJA-MEDIA (DDT overlap needs reconciliation)

### N2.3 — Tree Decomposition Chain (Layer 4) [CRITICO]
- **Archivos**: `SuperHash/TrustHash/TreeDecomp.lean` (nuevo, ~600 LOC)
- **Source**:
  - `TreeDecomp.lean` (138 LOC) — tree decomposition structure
  - `NiceTreeConvert.lean` (120 LOC) — standard form conversion
  - `EliminationOrder.lean` (92 LOC) — greedy min-degree elimination
  - `TWBridge.lean` (117 LOC) — treewidth bridge theorems
  - `TrailBridge.lean` (113 LOC) — differential trail bridge
- **Deps**: N2.1
- **Dificultad**: MEDIA (graph algorithms need careful adaptation)

### N2.4 — Security DP Chain (Layer 5) [CRITICO]
- **Archivos**: `SuperHash/TrustHash/SecurityDP.lean` (nuevo, ~900 LOC)
- **Source**:
  - `DP/NiceTree.lean` (213 LOC) — NiceNode inductive + runDP
  - `DP/DPOperations.lean` (216 LOC) — leaf/introduce/forget/join
  - `DP/CryptoCost.lean` (161 LOC) — crypto cost functions for DP
  - `DP/DPBridge.lean` (135 LOC) — DP ↔ security bridge
  - `DP/SecurityDP.lean` (158 LOC) — `securityDP(δ, d, tree)`
- **Deps**: N2.3
- **Dificultad**: MEDIA-ALTA (core mathematical content)

### N2.5 — Pipeline Verdict (Layer 6) [CRITICO]
- **Archivos**: `SuperHash/TrustHash/PipelineVerdict.lean` (nuevo, ~700 LOC)
- **Source**:
  - `Pipeline/PipelineVerdict.lean` (190 LOC) — `computeVerdict = min(generic, structural)`
  - `Pipeline/StructuralPipeline.lean` (150 LOC) — structural cost computation
  - `Pipeline/GenericFloorPipeline.lean` (168 LOC) — birthday/GBP/Joux floor
  - `Pipeline/WideTrailPipeline.lean` (153 LOC) — wide trail cost
  - `Pipeline/ComputeInstances.lean` (185 LOC) — AES/Poseidon/PRESENT instances
- **Deps**: N2.4, N2.2
- **Dificultad**: MEDIA

### N2.6 — TrustHash Integration Tests [HOJA]
- **Archivos**: `Tests/NonVacuity/TrustHashDP.lean` (nuevo)
- **Deps**: N2.5
- **Entregables**:
  - AES verdict via DP = 62 bits (structural, matches TrustHash)
  - Poseidon verdict via DP = 25 bits (weakness detected)
  - `#eval computeVerdict aesSpec` produces non-trivial result
  - Comparison: v2.8 approximation vs v2.9 DP-based (should agree or DP should be tighter)

---

## DAG

```
FASE 1 (Saturation)      FASE 2 (TrustHash DP)
N1.1 ──→ N1.2            N2.1 ──→ N2.2 ──→ N2.3 ──→ N2.4 ──→ N2.5 ──→ N2.6
```

Las dos fases son INDEPENDIENTES — pueden ejecutarse en paralelo.

## Bloques de Ejecución

| Bloque | Nodos | Tipo | Ejecución | Esfuerzo |
|--------|-------|------|-----------|----------|
| **B1** | N1.1 | CRITICO | Secuencial | 30 min |
| **B2** | N1.2 | HOJA | Secuencial | 30 min |
| **B3** | N2.1 | FUND | Secuencial | 1-2h |
| **B4** | N2.2 | FUND | Secuencial | 1-2h |
| **B5** | N2.3 | CRITICO | Secuencial | 1-2h |
| **B6** | N2.4 | CRITICO | Secuencial | 2-3h |
| **B7** | N2.5, N2.6 | CRIT+HOJA | Paralelo | 1-2h |

**Total**: 7 bloques, 8 nodos, ~3,720 LOC nuevos + 3 líneas modificadas

---

## Riesgos

| Riesgo | Nivel | Mitigación |
|--------|-------|-----------|
| TrustHash 4.16→4.28 API differences | BAJO | Shim probado en v2.8 + L-489 |
| DP chain complexity | MEDIO | Copy verbatim, adapt namespaces only |
| HashSpec ≠ CryptoSemantics types | MEDIO | Bridge adapter (~100 LOC) |
| saturateF con reglas produce e-graph grande | BAJO | Fuel limit ya parametrizado |
| ~9 bugs en 6.2K LOC (L-523) | MEDIO | Build incremental por layer |

---

## Lecciones

| ID | Aplicación |
|----|-----------|
| L-523 | ~1 bug/700 LOC en adaptaciones |
| L-489 | HashMap API stable |
| L-513 | Compositional pipeline proofs |
| L-544 | K_n treewidth modeling |
