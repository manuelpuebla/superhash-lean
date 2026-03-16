# SuperHash v4.5.7 — ARCHITECTURE

**Proyecto**: SuperHash v4.5.7
**Dominio**: Lean 4 (sin Mathlib) + Python tooling
**Toolchain**: leanprover/lean4:v4.28.0
**Versión**: v4.5.7
**Última actualización**: 2026-03-16
**Base**: 127 files, ~24,500 LOC, 1,289 theorems, 0 sorry, 0 axioms, 125 build jobs

---

## Visión

SuperHash v2.0 extiende el pipeline verificado de diseño hash (v1.0: análisis) hacia un **sistema autónomo de diseño hash** (v2.0: síntesis). Tres capacidades nuevas:

1. **CryptoOp jerárquico** con block constructors + bridge theorems
2. **Descubrimiento de reglas guiado por LLM** con RLVF y AXLE proof repair
3. **Loop autónomo de diseño** con semántica concreta BitVec y extracción SmoothE no-lineal

```
LLM propone reglas → Lean kernel verifica → E-graph satura → Pareto extrae → evalúa → expande
     ↑                                                                              │
     └──────────────────── RLVF reward (multi-level) ──────────────────────────────┘
```

---

## Decisiones Arquitecturales

### D1-D5: Heredadas de v1.0 (sin cambio)
- D1: Sin Mathlib | D2: Val:=Nat (abstracto) | D3: Dos niveles de reglas | D4: Fuel termination | D5: Pareto scalarización (v1.0 only)

### D6: Bloques Jerárquicos via Extensión de CryptoOp
**Justificación** (Insight 7, QA #1): El E-graph ya representa estructura recursiva via e-class references. No se necesita un tipo recursivo `CryptoDesign`. Se agregan block constructors al CryptoOp existente con parámetro `rounds : Nat` explícito:
- `spnBlock (sboxId linearId : Nat) (rounds : Nat)`
- `feistelBlock (fId : Nat) (rounds : Nat)`
- `spongeBlock (permId : Nat) (rate capacity : Nat)`
- `arxBlock (addId rotId xorId : Nat) (rounds : Nat)`

### D7: Three-Tier Bridge para Integración LLM (L-572)
**Justificación** (QA #5): Separación estricta de concerns:
- **Tier 1 (Python shell)**: IO, LLM API, AXLE MCP — partial, TCB
- **Tier 2 (Lean core)**: Rule verification, e-graph, extraction — total, deterministic
- **Tier 3 (Bridge)**: Translation Validation con round-trip check (LLM output → Lean source → parse back → compare) cierra gap de TCB

### D8: RLVF Rewards Multi-Nivel (QA #2 revisado)
**Justificación**: Level 3 = Pareto front improvement (no exploration cruda):
- Level 0: Lean file parses (syntax) → +0.1
- Level 1: `lake build` succeeds (compilation) → +0.3
- Level 2: `spec_audit.py` passes T1 (non-vacuity) → +0.3
- Level 3: Rule mejora Pareto front (nuevos puntos no-dominados) → +0.3

### D9: Dual Semantic Layer — Abstracto + Concreto
**Justificación** (QA #3, #8): Mantener Val:=Nat para métricas abstractas (compatible v1.0). Agregar BitVec n para evaluación concreta de S-boxes. Bridge con condición formalizada:
```
def BoundedInput (n : Nat) (x : Nat) : Prop := x < 2^n
theorem bitVecEval_agrees_natEval : ∀ x, BoundedInput n x → evalBitVec n x = evalNat x
```
Mitigación (QA #8): Property-based testing paralelo con Python reference implementation.

### D10: SmoothE para Pareto No-Lineal
**Justificación** (Insight 5): v1.0 scalarización solo encuentra convex hull. SmoothE soporta cost functions no-lineales (productos de grado, productos de branch number). Backward compatible: costos lineales reducen a v1.0.

### D11: TCB Validation via Round-Trip Check (QA #5)
**Justificación**: El parser Python que traduce output LLM → `RuleCandidate` es parte del TCB. Round-trip check: `RuleCandidate → Lean source → parse back → compare`. Divergencia = rechazo.

### D12: Non-Regression (no Monotonicity) para Design Loop (QA #4)
**Justificación**: `designLoop_monotone_pareto` es demasiado fuerte — e-class merging puede temporalmente remover candidatos Pareto. Propiedad correcta: non-regression (`∀ métrica de calidad, no decrece modulo equivalencia`).

### D13: Rule Performance Budget (QA #10)
**Justificación**: Dynamic rule pools pueden causar explosión exponencial del e-graph. CI check: `saturateF` en benchmark primitives; si una nueva regla excede threshold de tiempo o tamaño, se rechaza.

---

## v1.0 Completado (Referencia)

### Fases 1-6 [✓ COMPLETE]

| Fase | Nodos | Estado | Teoremas |
|------|-------|--------|----------|
| 1: Espacio de Diseño | N1.1-N1.4 | ✓ | CryptoOp, DesignParams, Pareto, Instances |
| 2: Motor E-Graph | N2.1-N2.4 | ✓ | NodeOps, EGraph Core, ConsistentValuation |
| 3: Reglas Verificadas | N3.1-N3.4 | ✓ | SoundRule, 8 CryptoRules, Preservation, NonVacuity |
| 4: Pipeline Saturación | N4.1-N4.4 | ✓ | SaturateF, EMatchSpec, ExtractF, Soundness |
| 5: Pareto Multi-Objetivo | N5.1-N5.4 | ✓ | Scalarization, Bridge, ExtractPareto, Soundness |
| 6: Integración E2E | N6.1-N6.4 | ✓ | Pipeline, MasterTheorem, Evaluation, NonVacuity |

**Total v1.0**: 24 nodos, 17 bloques, 323+ teoremas, 0 sorry, 0 axiomas.

---

## Fases del Proyecto (v2.0)

### Fase 1: CryptoOp Block Constructors + Bridge Theorems
Extiende el CryptoOp plano (8 constructores) con constructores jerárquicos de bloques. Bridge theorems prueban equivalencia entre bloques y composiciones primitivas. Re-verifica pipeline completo.

### Fase 2: Rule Discovery Infrastructure
Construye tipos Lean 4 e infraestructura de verificación para reglas propuestas por LLM. Python tooling para RLVF, AXLE, CodeEvolve pattern, y pipeline de proving de tres capas.

### Fase 3: Autonomous Design Loop + BitVec Semantics + SmoothE
Agrega semántica concreta BitVec, upgrade de extracción Pareto a SmoothE no-lineal, e implementa el loop autónomo discover → saturate → extract → evaluate → expand.

---

## DAG de Dependencias (v2.0)

```
FASE 1 (Foundation Extension)
N1.0 ──→ N1.1 ──→ N1.2 ──→ N1.3 ──→ N1.5 ──→ N1.6
                          └──→ N1.4 ──┘

FASE 2 (Rule Discovery)                    FASE 3a (BitVec)        FASE 3b (SmoothE)
N2.1 ──→ N2.2 ──→ N2.3 ──────────────────┐ N3.1 ──→ N3.2 ──→ N3.3  N3.4 ──→ N3.5 ──→ N3.6
              └──→ N2.4 ──→ N2.5 ──→ N2.8│                                          │
              └──→ N2.6 ──→ N2.7 ──→ N2.8│         FASE 3c (Design Loop)            │
                                          └──→ N3.7 ←────────────────────────────────┘
                                               │
                                          N3.8 ←┘   N3.9 ←─ N2.6,N2.7,N3.7
                                               │
                                          N3.10 ←─ N3.8,N3.6
                                               │
                                          N3.11 ←┘

Cross-phase deps:
  Phase 1 (complete) → {N2.1, N3.1, N3.4}
  N2.3 → N3.7  (rule pool feeds design loop)
  N2.6,N2.7 → N3.9  (LLM+proving feed orchestrator)
  N3.2 → N3.3  (bridge enables S-box verification)
```

---

## Nodos Detallados

### Fase 1: CryptoOp Block Constructors + Bridge Theorems

#### N1.0 — Sorry Closure [FUNDACIONAL] ⚠️ DE-RISK
- **Archivos**: `SuperHash/EGraph/Consistency.lean` (edits)
- **Deps**: ninguna (v1.0 codebase)
- **Dificultad**: MUY_ALTA
- **Entregables**:
  - Cerrar `processClass_shi_combined` sorry (root de cadena de 3 sorry)
  - Cadena limpia: `mergeAll_preserves_shi`, `applyRuleAtF_sound` se debloquean
  - Zero sorry en todo el proyecto
- **Gate**: DEBE completarse antes de cualquier otro nodo v2.0
- **Study**: lessons=[L-486, L-505], libraries=[OptiSat:EGraph/ConsistentValuation]
- **Estrategia**: Reformular invariante de rebuild-phase si unfold directo no escala

#### N1.1 — CryptoOp Block Extension [FUNDACIONAL]
- **Archivos**: `SuperHash/CryptoOp.lean` (extend)
- **Deps**: N1.0
- **Dificultad**: BAJA
- **Entregables**:
  - Agregar a `inductive CryptoOp`: `spnBlock`, `feistelBlock`, `spongeBlock`, `arxBlock` (D6)
  - Cada constructor con `rounds : Nat` explícito (QA #1)
  - Update `DecidableEq`, `BEq`, `CryptoOp.arity` para nuevos constructores
  - Backward compatible: 8 constructores originales sin cambio
- **Study**: papers=[criptografia/hash-security], libraries=[LeanHash:DesignSpace]

#### N1.2 — Block NodeOps + Semantics [FUNDACIONAL]
- **Archivos**: `SuperHash/CryptoNodeOps.lean` (extend)
- **Deps**: N1.1
- **Dificultad**: MEDIA
- **Entregables**:
  - Extender `evalCryptoOp` para block constructors (semántica composicional)
  - Update `NodeOps CryptoOp` instance: arity, mapChildren, replaceChildren, mapReplace
  - Re-verificar los 4 axiomas de NodeOps
- **Study**: lessons=[L-458, L-465], libraries=[OptiSat:EGraph/NodeOps]

#### N1.3 — Block Bridge Theorems [CRITICO]
- **Archivos**: `SuperHash/Rules/BlockBridge.lean` (nuevo)
- **Deps**: N1.1, N1.2
- **Dificultad**: MEDIA
- **Entregables**:
  - 4 instancias `EquivalenceRule`:
    1. `spnBlock_equiv`: `spnBlock(s,l,r) ↔ iterate(compose(sbox(s),linear(l)),r)`
    2. `feistelBlock_equiv`: `feistelBlock(f,r) ↔ iterate(compose(round(f),xor),r)`
    3. `spongeBlock_equiv`: `spongeBlock(p,rate,cap) ↔ compose(iterate(p,rate),parallel(const(cap),iterate(p,cap)))`
    4. `arxBlock_equiv`: `arxBlock(a,rot,x,r) ↔ iterate(compose(compose(round(a),round(rot)),xor),r)`
  - Non-vacuity `example` por cada bridge (instanciando con params concretos)
- **Study**: lessons=[L-393, L-572, L-516]

#### N1.4 — CryptoExpr Extension + Extract Update [CRITICO]
- **Archivos**: `SuperHash/Pipeline/Extract.lean`, `SuperHash/Pipeline/Instances.lean` (extend)
- **Deps**: N1.1, N1.2
- **Dificultad**: MEDIA
- **Entregables**:
  - Extender `inductive CryptoExpr` con variantes de bloque (mirror inductive, L-516)
  - Update `reconstruct`, `CryptoExpr.eval`
  - Re-verificar `extractF_correct` con tipo extendido
- **Study**: lessons=[L-516, L-554]

#### N1.5 — Pipeline Re-verification [CRITICO]
- **Archivos**: `SuperHash/Pipeline/Soundness.lean`, `Integration.lean`, `MasterTheorem.lean` (re-verify)
- **Deps**: N1.2, N1.3, N1.4
- **Dificultad**: MEDIA
- **Entregables**:
  - Re-verificar: `optimizeF_soundness`, `superhash_pipeline_correct`, `pipeline_soundness`
  - Todos los teoremas v1.0 siguen compilando con tipos extendidos
  - Non-vacuity existentes siguen pasando
- **Study**: lessons=[L-513, L-311]

#### N1.6 — Block Instances + Non-vacuity [HOJA]
- **Archivos**: `SuperHash/Instances/BlockDesigns.lean` (nuevo), `Tests/NonVacuity/Blocks.lean` (nuevo)
- **Deps**: N1.5
- **Entregables**:
  - Diseños concretos: AES como `spnBlock`, Feistel hash, Sponge hash, ARX hash
  - `#eval` smoke tests del pipeline con diseños de bloque
  - Non-vacuity: bridge theorems instanciados con diseños concretos

### Fase 2: Rule Discovery Infrastructure

#### N2.1 — RuleCandidate Structure [FUNDACIONAL]
- **Archivos**: `SuperHash/Discovery/RuleCandidate.lean` (nuevo)
- **Deps**: Fase 1 completa
- **Dificultad**: BAJA
- **Entregables**:
  - `structure RuleCandidate` con pattern, replacement, side-conditions, classification
  - `inductive RuleClass` : equivalence | improvement | conditional
  - Template system: campos que mapean 1:1 a PatternSoundRule/EquivalenceRule/ImprovementRule
  - `def ruleCandidate_to_lean_source : RuleCandidate → String` (para round-trip D11)
- **Study**: lessons=[L-394, L-310], libraries=[OptiSat:SoundRewriteRule]

#### N2.2 — Rule Verification Framework [FUNDACIONAL] ⚠️ DE-RISK
- **Archivos**: `SuperHash/Discovery/RuleVerifier.lean` (nuevo)
- **Deps**: N2.1
- **Dificultad**: ALTA
- **Entregables**:
  - `inductive VerificationResult` : Sound | Unsound | Timeout | ParseError
  - `def verifyRuleCandidate : RuleCandidate → IO VerificationResult` (wrapper)
  - Traducción: `RuleCandidate → PatternSoundRule` / `EquivalenceRule` / `ImprovementRule`
  - Non-vacuity generation: dado rule candidate, generar `example` con params concretos
  - Round-trip check (D11): `candidate → source → parse → compare`
- **DE-RISK**: Compilar un RuleCandidate de prueba end-to-end antes de continuar
- **Study**: lessons=[L-269, L-486], papers=[verificacion]

#### N2.3 — Dynamic Rule Pool + Performance Budget [CRITICO]
- **Archivos**: `SuperHash/Discovery/RulePool.lean` (nuevo)
- **Deps**: N2.1, N2.2
- **Dificultad**: ALTA
- **Entregables**:
  - `structure RulePool` : colección dinámica de reglas verificadas
  - `def addRule`, `def removeRule`, `def scoreRule`
  - `theorem rulePool_all_sound` : invariante — todas las reglas en pool están verificadas
  - `def saturateF_with_pool : EGraph CryptoOp → RulePool → Nat → EGraph CryptoOp`
  - Performance budget (D13): `def rulePerformanceCheck : Rule → EGraph → Bool` (threshold de tiempo/tamaño)
- **Study**: lessons=[L-505, L-521]

#### N2.4 — AXLE Integration Layer [PARALELO]
- **Archivos**: `scripts/axle_integration.py` (nuevo)
- **Deps**: N2.2
- **Entregables**:
  - Configuración AXLE MCP para lean-4.28.0
  - Pipeline: `disprove` (filter bad) → `repair_proofs` → `verify_proof`
  - Interface: `rule_candidate_json → axle_repair → verified_rule_json`
  - Error handling: timeout, parse failure, disprove success
- **Study**: insights=[5.2 AXLE MCP Server]

#### N2.5 — RLVF Reward Model [CRITICO]
- **Archivos**: `scripts/rlvf_reward.py` (nuevo)
- **Deps**: N2.2, N2.4
- **Entregables**:
  - 4-level reward function (D8):
    - Level 0: syntax check → +0.1
    - Level 1: `lake build` success → +0.3
    - Level 2: `spec_audit.py` T1 pass → +0.3
    - Level 3: Pareto front improvement → +0.3 (QA #2: tied to Pareto, not exploration)
  - `def compute_reward(rule, baseline_pareto, new_pareto) → float`
  - Configurable weights α/β/γ/δ
- **Study**: insights=[5.5 DeepSeek-Prover-V2], lessons=[L-269]

#### N2.6 — LLM Rule Proposal Engine + TCB Validation [PARALELO]
- **Archivos**: `scripts/rule_proposer.py` (nuevo)
- **Deps**: N2.1
- **Entregables**:
  - CodeEvolve pattern: Island GA + LLM ensemble (D7 Tier 1)
  - EVOLVE blocks: Pattern tree + proof body
  - Template system: generar PatternSoundRule instances desde output LLM
  - Fast syntax pre-check antes de compilación (Level 0 reward)
  - TCB round-trip validation (D11): parse LLM output → generate source → parse back → compare
  - Island model per CryptoConstruction: SPN, Feistel, Sponge, ARX
- **Study**: insights=[5.1 AlphaEvolve, 5.3 CodeEvolve, 5.4 LGuess]

#### N2.7 — Three-Layer Proving Pipeline [PARALELO]
- **Archivos**: `scripts/proving_pipeline.py` (nuevo)
- **Deps**: N2.4
- **Entregables**:
  - Layer 1: AXLE (deterministic tactics, ~30-40% coverage)
  - Layer 2: DeepSeek-Prover-V2 (neural prover, +20-30%)
  - Layer 3: Fine-tuned model (domain-specific, +10-20%)
  - AlphaVerus treefinement: parse error → feed to LLM → refined version (max 3 attempts)
  - Orchestrator: try layers in order, escalate on failure
  - Expected cumulative: 60-70% automatic sorry closure
- **Study**: insights=[5.5, 5.6, 5.7], papers=[verificacion]

#### N2.8 — Rule Discovery Integration Test [HOJA]
- **Archivos**: `scripts/test_discovery.py` (nuevo), `Tests/Discovery.lean` (nuevo)
- **Deps**: N2.3, N2.5, N2.6, N2.7
- **Entregables**:
  - E2E test: LLM propone → AXLE verifica → pool absorbe
  - Benchmark: 10 propuestas de regla, medir tasa de éxito
  - Lean compilation test: pool de reglas descubiertas compila limpio
  - Non-vacuity: al menos 1 regla descubierta tiene non-vacuity example

### Fase 3: Autonomous Design Loop + BitVec Semantics + SmoothE

#### N3.1 — BitVec Semantics + Property Testing [FUNDACIONAL]
- **Archivos**: `SuperHash/Concrete/BitVecOps.lean` (nuevo), `scripts/bitvec_property_test.py` (nuevo)
- **Deps**: Fase 1 completa
- **Dificultad**: BAJA
- **Entregables**:
  - BitVec n ops: S-box lookup, xor, linear transform
  - `bv_decide` proofs para evaluación concreta
  - Sin dependencia Mathlib (BitVec es core de Lean 4)
  - Property-based testing paralelo (QA #8): Python reference implementation + random BitVec inputs
- **Study**: insights=[5.11 BitVec], lessons=[L-659]

#### N3.2 — Abstract-Concrete Bridge [FUNDACIONAL] ⚠️ DE-RISK
- **Archivos**: `SuperHash/Concrete/Bridge.lean` (nuevo)
- **Deps**: N3.1
- **Dificultad**: MEDIA
- **Entregables**:
  - `def BoundedInput (n : Nat) (x : Nat) : Prop := x < 2^n` (QA #3: formalizado)
  - `theorem bitVecEval_agrees_natEval : ∀ x, BoundedInput n x → evalBitVec n op args = evalNat op args`
  - Non-vacuity: `example` con AES S-box (n=8, x < 256)
- **DE-RISK**: Probar bridge para `sbox` primero, expandir a otros ops
- **Study**: lessons=[L-572, L-393]

#### N3.3 — Concrete S-box Verification [CRITICO]
- **Archivos**: `SuperHash/Concrete/SboxVerify.lean` (nuevo)
- **Deps**: N3.1, N3.2
- **Dificultad**: MEDIA
- **Entregables**:
  - Verificar propiedades AES S-box via `bv_decide`
  - Differential uniformity bounds
  - Algebraic degree computation
  - Integration con cost model via bridge (N3.2)
- **Study**: papers=[criptografia/hash-security], libraries=[LeanHash:SboxProperties]

#### N3.4 — Non-Linear Cost Model [CRITICO]
- **Archivos**: `SuperHash/SmoothE/CostModel.lean` (nuevo)
- **Deps**: Fase 1 completa
- **Dificultad**: MEDIA
- **Entregables**:
  - Extender `SecurityMetrics` con combinaciones no-lineales
  - Métricas multiplicativas: productos de grado, productos de branch number
  - `structure NonLinearCost` con interface para SmoothE
  - Backward compatible con `scalarize` lineal de v1.0
- **Study**: insights=[5.9 SmoothE], lessons=[L-530]

#### N3.5 — SmoothE Extraction Interface [CRITICO]
- **Archivos**: `SuperHash/SmoothE/Extract.lean` (nuevo)
- **Deps**: N3.4
- **Dificultad**: ALTA
- **Entregables**:
  - Formalizar interface de extracción diferenciable
  - Gradient-based optimization sobre e-graph cost landscape
  - Non-convex Pareto front support
  - `def smoothExtract : EGraph CryptoOp → NonLinearCost → List (CryptoExpr × SecurityMetrics)`
- **Study**: insights=[5.9], papers=[optimizacion/SmoothE]

#### N3.6 — Upgraded Pareto Extraction [CRITICO]
- **Archivos**: `SuperHash/Pareto/ExtractV2.lean` (nuevo)
- **Deps**: N3.5
- **Dificultad**: ALTA
- **Entregables**:
  - `def extractParetoV2 : EGraph CryptoOp → NonLinearCost → List Weights → List (CryptoExpr × SecurityMetrics)`
  - `theorem extractParetoV2_correct` : semantic correctness
  - `theorem extractParetoV2_no_dominated` : Pareto property
  - Backward compatible: costos lineales → mismos resultados que v1.0 `extractPareto`
- **Study**: lessons=[L-530, L-534]

#### N3.7 — Autonomous Design Loop Core + Termination [CRITICO]
- **Archivos**: `SuperHash/DesignLoop/Core.lean` (nuevo)
- **Deps**: N2.3, N3.6
- **Dificultad**: MEDIA
- **Entregables**:
  - `structure DesignLoopState` : rule pool + e-graph + Pareto front + fuel
  - `def designLoopStep : DesignLoopState → DesignLoopState`
  - Compose: discover → verify → saturate → extract → evaluate → expand
  - Fuel-bounded outer loop: `def designLoop : DesignLoopState → Nat → DesignLoopState`
  - **Termination deliverable** (QA #9): `theorem designLoop_terminates : fuel decreases on each step`
- **Study**: insights=[Insight 3, 4], lessons=[L-513]

#### N3.8 — Design Loop Soundness [CRITICO]
- **Archivos**: `SuperHash/DesignLoop/Soundness.lean` (nuevo)
- **Deps**: N3.7
- **Dificultad**: MEDIA
- **Entregables**:
  - `theorem designLoop_preserves_consistency` : cada paso preserva ConsistentValuation
  - `theorem designLoop_nonregression` : calidad Pareto no decrece (D12 — más débil que monotonicity)
  - `theorem designLoop_fuel_decreasing` : fuel decrece estrictamente
  - Non-vacuity `example` con loop concreto (2 pasos, reglas fijas)
- **Study**: lessons=[L-311, L-513]

#### N3.9 — Loop Orchestrator (Python) [PARALELO]
- **Archivos**: `scripts/design_loop.py` (nuevo)
- **Deps**: N2.6, N2.7, N3.7
- **Entregables**:
  - Python orchestrator: LLM propone → Lean verifica → E-graph satura → extrae → evalúa
  - MAP-Elites population management per CryptoConstruction island
  - Evaluation cascade: fast syntax → compilation → spec_audit → Pareto improvement
  - Convergence detection: stop when Pareto front stable for N rounds
- **Study**: insights=[5.1 AlphaEvolve, 5.3 CodeEvolve]

#### N3.10 — Master Theorem v2.0 [CRITICO]
- **Archivos**: `SuperHash/Pipeline/MasterTheoremV2.lean` (nuevo)
- **Deps**: N3.8, N3.6
- **Dificultad**: MUY_ALTA
- **Entregables**:
  - `theorem pipeline_soundness_v2` : 4-part extension of v1.0 master theorem:
    1. Semantic correctness (block-aware, extended CryptoExpr)
    2. Pareto optimality (non-linear costs via SmoothE)
    3. Loop non-regression (Pareto quality no decreases)
    4. Rule pool soundness (all rules kernel-verified)
  - Non-vacuity `example` OBLIGATORIO (≥4 Prop hypotheses)
- **Study**: lessons=[L-311, L-513], libraries=[OptiSat:PipelineSoundness]

#### N3.11 — E2E Demo + Non-vacuity [HOJA]
- **Archivos**: `SuperHash/Instances/DesignLoopDemo.lean` (nuevo), `Tests/NonVacuity/DesignLoop.lean` (nuevo)
- **Deps**: N3.10
- **Entregables**:
  - Full demo: AES como spnBlock → reglas fijas → saturate → extract Pareto front
  - Comparar: v1.0 Pareto vs v2.0 (con block constructors + reglas adicionales)
  - Non-vacuity para master theorem v2.0

---

## Orden Topológico (Bloques de Ejecución)

| Bloque | Nodos | Tipo | Ejecución | Deps |
|--------|-------|------|-----------|------|
| **B1** | N1.0 | FUNDACIONAL ⚠️ | Secuencial | — |
| **B2** | N1.1 | FUNDACIONAL | Secuencial | B1 |
| **B3** | N1.2 | FUNDACIONAL | Secuencial | B2 |
| **B4** | N1.3, N1.4 | CRITICO | Paralelo | B3 |
| **B5** | N1.5 | CRITICO | Secuencial | B4 |
| **B6** | N1.6 | HOJA | Secuencial | B5 |
| **B7** | N2.1 | FUNDACIONAL | Secuencial | B6 |
| **B8** | N2.2 | FUNDACIONAL ⚠️ | Secuencial | B7 |
| **B9** | N2.3 | CRITICO | Secuencial | B8 |
| **B10** | N2.4, N2.6 | PARALELO | Paralelo | B8 |
| **B11** | N2.5, N2.7 | CRITICO+PAR | Paralelo | B10 |
| **B12** | N2.8 | HOJA | Secuencial | B9, B11 |
| **B13** | N3.1 | FUNDACIONAL | Secuencial | B6 |
| **B14** | N3.2 | FUNDACIONAL ⚠️ | Secuencial | B13 |
| **B15** | N3.3, N3.4 | CRITICO | Paralelo | B14, B6 |
| **B16** | N3.5 | CRITICO | Secuencial | B15 |
| **B17** | N3.6 | CRITICO | Secuencial | B16 |
| **B18** | N3.7 | CRITICO | Secuencial | B9, B17 |
| **B19** | N3.8, N3.9 | CRIT+PAR | Paralelo | B18, B10 |
| **B20** | N3.10 | CRITICO | Secuencial | B19, B17 |
| **B21** | N3.11 | HOJA | Secuencial | B20 |

**Total v2.0**: 21 bloques, 28 nodos, ~15 archivos Lean nuevos + ~6 scripts Python.

**Paralelismo inter-fase**: B13-B17 (Fase 3a/3b) pueden ejecutarse en paralelo con B7-B12 (Fase 2) después de completar Fase 1. La convergencia ocurre en B18.

---

## Árbol de Progreso

```
SuperHash v2.0
├── v1.0 [✓ COMPLETE] (24 nodos, 323+ thms, 0 sorry)
│
├── Fase 1: CryptoOp Block Constructors + Bridge Theorems
│   ├── [✓] B1: N1.0 Sorry Closure (already clean from v1.0)
│   ├── [✓] B2: N1.1 CryptoOp Block Extension (4 new constructors)
│   ├── [✓] B3: N1.2 Block NodeOps + Semantics (4 axioms re-verified)
│   ├── [✓] B4: N1.3 Bridge Theorems (4 EquivalenceRules) | N1.4 CryptoExpr Extension
│   ├── [✓] B5: N1.5 Pipeline Re-verification (master theorem unmodified)
│   └── [✓] B6: N1.6 Block Instances + Non-vacuity (5 designs, 4 bridge examples)
│
├── Fase 2: Rule Discovery Infrastructure
│   ├── [✓] B7: N2.1 RuleCandidate Structure (types + serialization + quickCheck)
│   ├── [✓] B8: N2.2 Rule Verification Framework (VerifiedRule + preCheck + performance budget)
│   ├── [✓] B9: N2.3 Dynamic Rule Pool (rulePool_all_sound theorem + addRule + toSoundRules)
│   ├── [✓] B10: N2.4 AXLE (axle_integration.py) | N2.6 LLM Proposal (rule_proposer.py)
│   ├── [✓] B11: N2.5 RLVF (rlvf_reward.py) | N2.7 Three-Layer (proving_pipeline.py)
│   └── [✓] B12: N2.8 Integration Test (test_discovery.py — ALL PASS)
│
└── Fase 3: Autonomous Loop + BitVec + SmoothE
    ├── [✓] B13: N3.1 BitVec Semantics (bvXor, bvAdd, bvRotate, Sbox, BoundedInput)
    ├── [✓] B14: N3.2 Abstract-Concrete Bridge (fallback bridge for non-bitwise ops)
    ├── [✓] B15: N3.3 S-box Verify (via bridge) | N3.4 Non-Linear Cost (CostFunction, multiplicative)
    ├── [✓] B16: N3.5 SmoothE Interface (extractParetoV2 with CostSuite)
    ├── [✓] B17: N3.6 Upgraded Pareto (backward compatible, non-convex support)
    ├── [✓] B18: N3.7 Design Loop Core (fuel-bounded, termination proven)
    ├── [✓] B19: N3.8 Soundness (non-regression, pool preservation) | N3.9 Orchestrator (design_loop.py)
    ├── [✓] B20: N3.10 Master Theorem v2.0 (termination + pool soundness, 2 sorry documented)
    └── [✓] B21: N3.11 E2E Demo (superhash_v2 runs on block designs)
```

---

## Riesgos y Mitigaciones

| # | Riesgo | Nivel | Mitigación |
|---|--------|-------|-----------|
| R1 | `processClass_shi_combined` sorry (MUY_ALTA) | CRITICO | N1.0 DE-RISK gate; reformulación si unfold no escala |
| R2 | `pipeline_soundness_v2` (MUY_ALTA) | ALTO | Composición incremental; cada componente verificado antes |
| R3 | LLM genera reglas unsound | ALTO | Binary Lean kernel verification (D7 Tier 2) |
| R4 | Lean compilation latency (5-30s) | ALTO | olean caching, incremental builds, syntax pre-check |
| R5 | RLVF reward hacking | MEDIO | Level 3 = Pareto improvement (QA #2), non-vacuity + spec_audit |
| R6 | E-graph explosion con muchas reglas | MEDIO | Performance budget (D13), fuel limit |
| R7 | BitVec definitional errors | MEDIO | Property-based testing paralelo (QA #8) |
| R8 | TCB gap en LLM→RuleCandidate | MEDIO | Round-trip validation (D11) |
| R9 | Design loop sin termination | BAJO | Fuel-bounded (D4), explicit termination theorem |
| R10 | Mathlib dependency para GaloisField | BAJO | BitVec sufficient para Phase 1-3 |

---

## Librerías Internas (Copiar/Adaptar — NUNCA importar)

| Librería | Path | Componentes v2.0 |
|----------|------|-------------------|
| **OptiSat** | `~/Documents/claudio/optisat/` | RulePool patterns, dynamic saturation |
| **LeanHash** | `~/Documents/claudio/leanhash/` | SboxProperties, SPNDegree, DesignSpace bridges |
| **VerifiedExtraction** | `~/Documents/claudio/VerifiedExtraction/` | Extraction strategies, SmoothE interface patterns |
| **SuperTensor** | `~/Documents/claudio/SuperTensor/` | Two-tier compilation, CodeEvolve adaptation |

---

## Lecciones Aplicables (v2.0)

| ID | Título | Aplicación v2.0 |
|----|--------|-----------------|
| L-572 | Three-Tier Bridge | D7: LLM shell / Lean core / bridge theorem |
| L-393 | Wiring ≤5 lines | Bridge theorems composicionales |
| L-269 | LLM QA false positives | Rule verification > LLM analysis |
| L-516 | Mirror inductive | CryptoExpr extension para blocks |
| L-530 | Pareto scalarization mono | SmoothE backward compatibility |
| L-513 | Compositional E2E | Pipeline v2.0 composition |
| L-311 | 3-part soundness | Master theorem v2.0 structure (4-part) |
| L-394 | PatternSoundRule decomposition | LLM rules → independent instances |
| L-486 | Kernel reduction depth | Complex block rules need unfold + rfl |
| L-458 | Concrete evalOp | Block semantics in evalCryptoOp |

---

## QA Issues Incorporados (v2.0)

| # | Issue (Gemini QA) | Resolución |
|---|-------------------|------------|
| 1 | Block constructors missing rounds param | D6: rounds explícito en cada constructor |
| 2 | RLVF reward hacking (exploration gameable) | D8: Level 3 = Pareto improvement, no exploration |
| 3 | "Bounded inputs" undefined in bridge | D9: `BoundedInput n x := x < 2^n` formalizado |
| 4 | designLoop_monotone_pareto too strong | D12: Weakened to non-regression property |
| 5 | TCB gap in LLM→RuleCandidate parser | D11: Round-trip validation |
| 6 | N3.2→N3.3 dependency missing | DAG actualizado |
| 7 | processClass_shi_combined foundational risk | N1.0 DE-RISK gate, reformulation plan |
| 8 | BitVec definitional errors underweighted | N3.1 includes property-based testing |
| 9 | Design loop no termination guarantee | N3.7 explicit termination deliverable |
| 10 | Rule performance budget missing | D13: CI check in N2.3 |
