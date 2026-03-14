# SuperHash v2.8 — ARCHITECTURE

**Proyecto**: SuperHash v2.8
**Base**: v2.7 (53 jobs, 0 sorry, NodeSemantics CryptoSemantics instance, AES DDT certified)
**Fuentes**: LeanHash (163 new thms), OptiSat (CompletenessSpec), TrustHash (fitness pipeline)
**Objetivo**: Integrar degree bounds + extraction completeness + TrustHash fitness bridge

---

## Visión

v2.8 cierra tres gaps:
1. **Boura-Canteaut bounds** (163 theorems de LeanHash) — grado algebraico formal en SuperHash
2. **Extraction completeness** (8 theorems de OptiSat) — probar que extractAuto siempre produce resultado
3. **TrustHash fitness bridge** — conectar el pipeline verificado de TrustHash como evaluador

---

## Fase 1: Boura-Canteaut Integration (Copy LeanHash)

### N1.1 — BouraCanteutBound [FUNDACIONAL]
- **Archivo**: `SuperHash/Crypto/BouraCanteutBound.lean` (nuevo)
- **Source**: Copiar/adaptar `~/Documents/claudio/leanhash/LeanHash/BouraCanteutBound.lean` (685 LOC, 55 thms)
- **Entregables**:
  - `bcd11Bound(n, degG, gamma)` — bound general BCD11
  - `bc13Bound(n, degG, invDeg)` — bound general BC13 (tighter for permutations)
  - `iteratedBcd11(n, degG, gamma, r)` — composición iterada r rondas
  - Monotonicity: `bcd11_mono_degG`, `bc13_mono_invDeg`
  - Concrete: AES, Keccak, Poseidon instances
  - 7 non-vacuity examples
- **Adaptación**: Namespace `LeanHash.BouraCanteutBound` → `SuperHash.BouraCanteutBound`. Imports: solo `SuperHash.Crypto.Semantics` (para tipos compartidos).
- **Dificultad**: BAJA (copy + namespace)

### N1.2 — HigherOrderDiff [PARALELO]
- **Archivo**: `SuperHash/Crypto/HigherOrderDiff.lean` (nuevo)
- **Source**: Copiar/adaptar `~/Documents/claudio/leanhash/LeanHash/HigherOrderDiff.lean` (711 LOC, 43 thms)
- **Entregables**:
  - `minVanishingDim = deg + 1` — derivative vanishing
  - `attackQueries = 2^(deg+1)` — attack complexity from degree
  - Zero-sum partition definitions + Keccak instances
  - Keccak degree tables (forward + backward)
- **Dificultad**: BAJA

### N1.3 — LinearLayerDegree [PARALELO]
- **Archivo**: `SuperHash/Crypto/LinearLayerDegree.lean` (nuevo)
- **Source**: Copiar/adaptar `~/Documents/claudio/leanhash/LeanHash/LinearLayerDegree.lean` (1030 LOC, 65 thms)
- **Entregables**:
  - `SPNParams` structure con proofs
  - Phase transition: `expansionRounds`, `expPhaseBound`, `linPhaseBound`
  - `Arrangement` classification (strong/weak)
  - `approxRSPN` — minimum rounds for full degree
  - Concrete: AES (R_SPN=2), MiMC, Poseidon
- **Dificultad**: BAJA

### N1.4 — Degree Integration Tests [HOJA]
- **Archivo**: `Tests/NonVacuity/DegreeBounds.lean` (nuevo)
- **Deps**: N1.1, N1.2, N1.3
- **Entregables**:
  - `#eval` tests: `bcd11Bound 128 0 4 = 96` (AES round 1)
  - `#eval` tests: `iteratedBcd11 128 0 4 3 = 126` (AES 3 rounds)
  - Non-vacuity: `attackQueries` for AES, Keccak, Poseidon
  - Integration: connect to `fitness` function via algebraicSecurityBits

---

## Fase 2: OptiSat Extraction Completeness

### N2.1 — Completeness Definitions [FUNDACIONAL]
- **Archivo**: `SuperHash/Pipeline/CompletenessSpec.lean` (nuevo)
- **Source**: Copiar/adaptar `~/Documents/claudio/optisat/LambdaSat/CompletenessSpec.lean` lines 37-95
- **Entregables**:
  - `def BestNodeChild` — child edge via bestNode pointers
  - `def AcyclicBestNodeDAG` — ranking function existence
  - `def BestCostLowerBound` — self-referential cost invariant
  - Helper: `foldl_ge_init`, `foldl_sum_ge_mem`
- **Dificultad**: BAJA (pure copy, generic over `Op`)

### N2.2 — Acyclicity + Fuel Sufficiency [CRITICO]
- **Archivo**: `SuperHash/Pipeline/CompletenessSpec.lean` (continuación)
- **Source**: Copiar/adaptar OptiSat lines 100-424
- **Deps**: N2.1
- **Entregables**:
  - `bestCostLowerBound_acyclic` — **G1**: LB + positive costs → acyclic DAG
  - `computeCostsF_bestCost_lower_bound` — cost computation preserves LB
  - `computeCostsF_acyclic` — cost computation produces acyclic DAG
  - `extractF_of_rank` — **G2**: ranking + fuel → extraction succeeds
  - `extractAuto_complete` — **fuel sufficiency**: extractAuto always produces result
- **Dificultad**: MEDIA (large proof ~300 LOC, but parametric — should compile with CryptoOp)

### N2.3 — Pipeline Crypto Composition [CRITICO]
- **Archivo**: `SuperHash/Pipeline/CryptoPipeline.lean` (nuevo)
- **Deps**: N2.2, CryptoNodeSemantics
- **Entregables**:
  - `def superhash_pipeline_crypto` — pipeline over CryptoSemantics rules
  - `theorem pipeline_soundness_crypto` — 3-part master theorem for CryptoSemantics:
    1. Semantic correctness (extracted designs evaluate to root CryptoSemantics)
    2. Pareto optimality
    3. Output bound
  - Composición: saturar con CryptoSemantics → extract con Nat via projectToNat bridge
  - Non-vacuity example con AES design
- **Dificultad**: MEDIA-ALTA (composición de polymorphic machinery, bridge CS→Nat)
- **Key insight**: Usar `optimizeF_soundness` (polymorphic) directamente, no reescribir

---

## Fase 3: TrustHash Fitness Bridge

### N3.1 — HashOp ↔ CryptoOp Translation [FUNDACIONAL]
- **Archivo**: `SuperHash/Bridge/HashOpBridge.lean` (nuevo)
- **Source**: Reference `~/Documents/claudio/TrustHash/TrustHash/HashOp.lean`
- **Entregables**:
  - `def cryptoOpToHashOp : CryptoOp → Option HashOp` — translation (Some for mapped ops, None for unsupported)
  - `def hashOpToCryptoOp : HashOp → Option CryptoOp` — reverse translation
  - Mapping: sbox↔sboxApply, linear↔mdsMix, compose↔compose, iterate↔roundFunc, const↔constOp
  - Keccak ops → None (unsupported in CryptoOp)
  - v2.0 blocks → decompose to primitives before translation
- **Dificultad**: MEDIA (mechanical mapping, ~200 LOC)

### N3.2 — TrustHash Fitness Wrapper [CRITICO]
- **Archivo**: `SuperHash/Bridge/TrustHashFitness.lean` (nuevo)
- **Source**: Reference TrustHash pipeline architecture
- **Deps**: N3.1
- **Entregables**:
  - `structure TrustHashVerdict` — mirrors TrustHash's security_level result
  - `def trustHashFitness : CryptoOp → TrustHashVerdict` — wrapper that:
    1. Translates CryptoOp → HashOp
    2. Applies TrustHash security_level formula
    3. Returns `min(genericFloor, structuralCost)`
  - `theorem trustHashFitness_monotone` — fitness monotone in security metrics
  - Concrete: AES verdict, Poseidon verdict
- **Dificultad**: MEDIA
- **Note**: Initially uses SIMPLIFIED TrustHash formula (not full pipeline). Full integration deferred.

### N3.3 — Bridge Tests [HOJA]
- **Archivo**: `Tests/NonVacuity/TrustHashBridge.lean` (nuevo)
- **Deps**: N3.1, N3.2
- **Entregables**:
  - Round-trip: `hashOpToCryptoOp (cryptoOpToHashOp op) = some op` for supported ops
  - Fitness: AES verdict matches expected (62 bits structural, 64 generic)
  - Poseidon: weakness detected (25 bits structural < 64 generic)

---

## DAG

```
FASE 1 (LeanHash copy)           FASE 2 (OptiSat completeness)
N1.1 ──┐                         N2.1 ──→ N2.2 ──→ N2.3
N1.2 ──┼──→ N1.4                                     │
N1.3 ──┘                    FASE 3 (TrustHash)       │
                             N3.1 ──→ N3.2 ──→ N3.3  │
                                                      └──→ (connects to N2.3)
```

## Bloques de Ejecución

| Bloque | Nodos | Tipo | Ejecución |
|--------|-------|------|-----------|
| **B1** | N1.1, N1.2, N1.3 | FUND+PAR | Paralelo (3 copy jobs) |
| **B2** | N1.4 | HOJA | Secuencial |
| **B3** | N2.1 | FUND | Secuencial |
| **B4** | N2.2 | CRITICO | Secuencial |
| **B5** | N2.3 | CRITICO | Secuencial |
| **B6** | N3.1 | FUND | Secuencial |
| **B7** | N3.2, N3.3 | CRIT+HOJA | Paralelo |

**Total**: 7 bloques, 10 nodos, ~7 archivos nuevos

---

## Estimación

| Archivo | LOC est. | Source |
|---------|----------|--------|
| Crypto/BouraCanteutBound.lean | ~685 | LeanHash copy |
| Crypto/HigherOrderDiff.lean | ~711 | LeanHash copy |
| Crypto/LinearLayerDegree.lean | ~1030 | LeanHash copy |
| Pipeline/CompletenessSpec.lean | ~400 | OptiSat copy+adapt |
| Pipeline/CryptoPipeline.lean | ~200 | New (composition) |
| Bridge/HashOpBridge.lean | ~200 | New (translation) |
| Bridge/TrustHashFitness.lean | ~150 | New (wrapper) |
| Tests (2 files) | ~100 | New |
| **Total** | **~3,476** | |

Theorems estimated: ~230+ (163 from LeanHash + 8 from OptiSat + ~60 new)

---

## Riesgos

| Riesgo | Nivel | Mitigación |
|--------|-------|-----------|
| LeanHash namespace conflicts | BAJO | Use SuperHash.Crypto.* namespace |
| OptiSat CompletenessSpec deps chain | MEDIO | Copy full dependency chain (BestNodeChild → acyclicity) |
| TrustHash Keccak ops unmapped | BAJO | Return None/default for unsupported |
| `pipeline_soundness_crypto` composition | ALTO | Use optimizeF_soundness (polymorphic) + projectToNat bridge |
| 3,476 LOC in one version | MEDIO | B1 is mechanical copy; most risk in B4-B5 |

---

## Lecciones Aplicables

| ID | Título | Aplicación |
|----|--------|-----------|
| L-523 | Library adaptation (~1 bug/700 LOC) | LeanHash/OptiSat copy → ~5 bugs expected |
| L-336 | Bridge with wrapper isomorphisms | HashOp ↔ CryptoOp translation |
| L-489 | HashMap API stable 4.16→4.28 | TrustHash migration safe |
| L-518 | ClassNodesSemantic extraction boundary | BestNodeInv interface |
| L-513 | Compositional E2E proofs | pipeline_soundness_crypto composition |
