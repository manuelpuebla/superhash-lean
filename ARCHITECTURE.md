# SuperHash v4.5.8 — ARCHITECTURE

**Project**: SuperHash v4.5.8
**Domain**: Lean 4 (no Mathlib) + Python tooling
**Toolchain**: leanprover/lean4:v4.28.0
**Version**: v4.5.8
**Last updated**: 2026-03-16
**Base**: 127 files, ~24,500 LOC, 1,289 theorems, 0 sorry, 0 axioms, 125 build jobs

---

## Vision

SuperHash v2.0 extends the verified hash design pipeline (v1.0: analysis) toward an **autonomous hash design system** (v2.0: synthesis). Three new capabilities:

1. **Hierarchical CryptoOp** with block constructors + bridge theorems
2. **LLM-guided rule discovery** with RLVF and AXLE proof repair
3. **Autonomous design loop** with concrete BitVec semantics and SmoothE non-linear extraction

```
LLM proposes rules --> Lean kernel verifies --> E-graph saturates --> Pareto extracts --> evaluates --> expands
     ^                                                                                                  |
     +--------------------------------- RLVF reward (multi-level) -------------------------------------+
```

---

## Architectural Decisions

### D1-D5: Inherited from v1.0 (unchanged)
- D1: No Mathlib | D2: Val:=Nat (abstract) | D3: Two-level rules | D4: Fuel termination | D5: Pareto scalarization (v1.0 only)

### D6: Hierarchical Blocks via CryptoOp Extension
**Rationale** (Insight 7, QA #1): The E-graph already represents recursive structure via e-class references. No recursive `CryptoDesign` type is needed. Block constructors are added to the existing CryptoOp with an explicit `rounds : Nat` parameter:
- `spnBlock (sboxId linearId : Nat) (rounds : Nat)`
- `feistelBlock (fId : Nat) (rounds : Nat)`
- `spongeBlock (permId : Nat) (rate capacity : Nat)`
- `arxBlock (addId rotId xorId : Nat) (rounds : Nat)`

### D7: Three-Tier Bridge for LLM Integration (L-572)
**Rationale** (QA #5): Strict separation of concerns:
- **Tier 1 (Python shell)**: IO, LLM API, AXLE MCP -- partial, TCB
- **Tier 2 (Lean core)**: Rule verification, e-graph, extraction -- total, deterministic
- **Tier 3 (Bridge)**: Translation Validation with round-trip check (LLM output -> Lean source -> parse back -> compare) closes TCB gap

### D8: Multi-Level RLVF Rewards (QA #2 revised)
**Rationale**: Level 3 = Pareto front improvement (not raw exploration):
- Level 0: Lean file parses (syntax) -> +0.1
- Level 1: `lake build` succeeds (compilation) -> +0.3
- Level 2: `spec_audit.py` passes T1 (non-vacuity) -> +0.3
- Level 3: Rule improves Pareto front (new non-dominated points) -> +0.3

### D9: Dual Semantic Layer -- Abstract + Concrete
**Rationale** (QA #3, #8): Keep Val:=Nat for abstract metrics (compatible with v1.0). Add BitVec n for concrete S-box evaluation. Bridge with formalized condition:
```
def BoundedInput (n : Nat) (x : Nat) : Prop := x < 2^n
theorem bitVecEval_agrees_natEval : forall x, BoundedInput n x -> evalBitVec n x = evalNat x
```
Mitigation (QA #8): Parallel property-based testing with Python reference implementation.

### D10: SmoothE for Non-Linear Pareto
**Rationale** (Insight 5): v1.0 scalarization only finds the convex hull. SmoothE supports non-linear cost functions (degree products, branch number products). Backward compatible: linear costs reduce to v1.0.

### D11: TCB Validation via Round-Trip Check (QA #5)
**Rationale**: The Python parser translating LLM output -> `RuleCandidate` is part of the TCB. Round-trip check: `RuleCandidate -> Lean source -> parse back -> compare`. Divergence = rejection.

### D12: Non-Regression (not Monotonicity) for Design Loop (QA #4)
**Rationale**: `designLoop_monotone_pareto` is too strong -- e-class merging can temporarily remove Pareto candidates. Correct property: non-regression (`for every quality metric, no decrease modulo equivalence`).

### D13: Rule Performance Budget (QA #10)
**Rationale**: Dynamic rule pools can cause exponential E-graph explosion. CI check: `saturateF` on benchmark primitives; if a new rule exceeds a time or size threshold, it is rejected.

---

## v1.0 Completed (Reference)

### Phases 1-6 [COMPLETE]

| Phase | Nodes | Status | Theorems |
|-------|-------|--------|----------|
| 1: Design Space | N1.1-N1.4 | ✓ | CryptoOp, DesignParams, Pareto, Instances |
| 2: E-Graph Engine | N2.1-N2.4 | ✓ | NodeOps, EGraph Core, ConsistentValuation |
| 3: Verified Rules | N3.1-N3.4 | ✓ | SoundRule, 8 CryptoRules, Preservation, NonVacuity |
| 4: Saturation Pipeline | N4.1-N4.4 | ✓ | SaturateF, EMatchSpec, ExtractF, Soundness |
| 5: Multi-Objective Pareto | N5.1-N5.4 | ✓ | Scalarization, Bridge, ExtractPareto, Soundness |
| 6: E2E Integration | N6.1-N6.4 | ✓ | Pipeline, MasterTheorem, Evaluation, NonVacuity |

**Total v1.0**: 24 nodes, 17 blocks, 323+ theorems, 0 sorry, 0 axioms.

---

## Project Phases (v2.0)

### Phase 1: CryptoOp Block Constructors + Bridge Theorems
Extends the flat CryptoOp (8 constructors) with hierarchical block constructors. Bridge theorems prove equivalence between blocks and primitive compositions. Re-verifies the full pipeline.

### Phase 2: Rule Discovery Infrastructure
Builds Lean 4 types and verification infrastructure for LLM-proposed rules. Python tooling for RLVF, AXLE, CodeEvolve pattern, and three-layer proving pipeline.

### Phase 3: Autonomous Design Loop + BitVec Semantics + SmoothE
Adds concrete BitVec semantics, upgrades Pareto extraction to SmoothE non-linear, and implements the autonomous discover -> saturate -> extract -> evaluate -> expand loop.

---

## Dependency DAG (v2.0)

```
PHASE 1 (Foundation Extension)
N1.0 --> N1.1 --> N1.2 --> N1.3 --> N1.5 --> N1.6
                         +--> N1.4 --+

PHASE 2 (Rule Discovery)                    PHASE 3a (BitVec)        PHASE 3b (SmoothE)
N2.1 --> N2.2 --> N2.3 -----------------+   N3.1 --> N3.2 --> N3.3   N3.4 --> N3.5 --> N3.6
              +--> N2.4 --> N2.5 --> N2.8|                                              |
              +--> N2.6 --> N2.7 --> N2.8|         PHASE 3c (Design Loop)               |
                                         +--> N3.7 <------------------------------------+
                                               |
                                          N3.8 <+   N3.9 <-- N2.6,N2.7,N3.7
                                               |
                                          N3.10 <-- N3.8,N3.6
                                               |
                                          N3.11 <+

Cross-phase deps:
  Phase 1 (complete) -> {N2.1, N3.1, N3.4}
  N2.3 -> N3.7  (rule pool feeds design loop)
  N2.6,N2.7 -> N3.9  (LLM+proving feed orchestrator)
  N3.2 -> N3.3  (bridge enables S-box verification)
```

---

## Detailed Nodes

### Phase 1: CryptoOp Block Constructors + Bridge Theorems

#### N1.0 — Sorry Closure [FOUNDATIONAL] -- DE-RISK
- **Files**: `SuperHash/EGraph/Consistency.lean` (edits)
- **Deps**: none (v1.0 codebase)
- **Difficulty**: VERY_HIGH
- **Deliverables**:
  - Close `processClass_shi_combined` sorry (root of 3-sorry chain)
  - Clean chain: `mergeAll_preserves_shi`, `applyRuleAtF_sound` unblocked
  - Zero sorry across the entire project
- **Gate**: MUST be completed before any other v2.0 node
- **Study**: lessons=[L-486, L-505], libraries=[OptiSat:EGraph/ConsistentValuation]
- **Strategy**: Reformulate rebuild-phase invariant if direct unfold does not scale

#### N1.1 — CryptoOp Block Extension [FOUNDATIONAL]
- **Files**: `SuperHash/CryptoOp.lean` (extend)
- **Deps**: N1.0
- **Difficulty**: LOW
- **Deliverables**:
  - Add to `inductive CryptoOp`: `spnBlock`, `feistelBlock`, `spongeBlock`, `arxBlock` (D6)
  - Each constructor with explicit `rounds : Nat` (QA #1)
  - Update `DecidableEq`, `BEq`, `CryptoOp.arity` for new constructors
  - Backward compatible: 8 original constructors unchanged
- **Study**: papers=[criptografia/hash-security], libraries=[LeanHash:DesignSpace]

#### N1.2 — Block NodeOps + Semantics [FOUNDATIONAL]
- **Files**: `SuperHash/CryptoNodeOps.lean` (extend)
- **Deps**: N1.1
- **Difficulty**: MEDIUM
- **Deliverables**:
  - Extend `evalCryptoOp` for block constructors (compositional semantics)
  - Update `NodeOps CryptoOp` instance: arity, mapChildren, replaceChildren, mapReplace
  - Re-verify all 4 NodeOps axioms
- **Study**: lessons=[L-458, L-465], libraries=[OptiSat:EGraph/NodeOps]

#### N1.3 — Block Bridge Theorems [CRITICAL]
- **Files**: `SuperHash/Rules/BlockBridge.lean` (new)
- **Deps**: N1.1, N1.2
- **Difficulty**: MEDIUM
- **Deliverables**:
  - 4 `EquivalenceRule` instances:
    1. `spnBlock_equiv`: `spnBlock(s,l,r) <-> iterate(compose(sbox(s),linear(l)),r)`
    2. `feistelBlock_equiv`: `feistelBlock(f,r) <-> iterate(compose(round(f),xor),r)`
    3. `spongeBlock_equiv`: `spongeBlock(p,rate,cap) <-> compose(iterate(p,rate),parallel(const(cap),iterate(p,cap)))`
    4. `arxBlock_equiv`: `arxBlock(a,rot,x,r) <-> iterate(compose(compose(round(a),round(rot)),xor),r)`
  - Non-vacuity `example` for each bridge (instantiated with concrete params)
- **Study**: lessons=[L-393, L-572, L-516]

#### N1.4 — CryptoExpr Extension + Extract Update [CRITICAL]
- **Files**: `SuperHash/Pipeline/Extract.lean`, `SuperHash/Pipeline/Instances.lean` (extend)
- **Deps**: N1.1, N1.2
- **Difficulty**: MEDIUM
- **Deliverables**:
  - Extend `inductive CryptoExpr` with block variants (mirror inductive, L-516)
  - Update `reconstruct`, `CryptoExpr.eval`
  - Re-verify `extractF_correct` with extended type
- **Study**: lessons=[L-516, L-554]

#### N1.5 — Pipeline Re-verification [CRITICAL]
- **Files**: `SuperHash/Pipeline/Soundness.lean`, `Integration.lean`, `MasterTheorem.lean` (re-verify)
- **Deps**: N1.2, N1.3, N1.4
- **Difficulty**: MEDIUM
- **Deliverables**:
  - Re-verify: `optimizeF_soundness`, `superhash_pipeline_correct`, `pipeline_soundness`
  - All v1.0 theorems still compile with extended types
  - Existing non-vacuity examples still pass
- **Study**: lessons=[L-513, L-311]

#### N1.6 — Block Instances + Non-vacuity [LEAF]
- **Files**: `SuperHash/Instances/BlockDesigns.lean` (new), `Tests/NonVacuity/Blocks.lean` (new)
- **Deps**: N1.5
- **Deliverables**:
  - Concrete designs: AES as `spnBlock`, Feistel hash, Sponge hash, ARX hash
  - `#eval` smoke tests of the pipeline with block designs
  - Non-vacuity: bridge theorems instantiated with concrete designs

### Phase 2: Rule Discovery Infrastructure

#### N2.1 — RuleCandidate Structure [FOUNDATIONAL]
- **Files**: `SuperHash/Discovery/RuleCandidate.lean` (new)
- **Deps**: Phase 1 complete
- **Difficulty**: LOW
- **Deliverables**:
  - `structure RuleCandidate` with pattern, replacement, side-conditions, classification
  - `inductive RuleClass` : equivalence | improvement | conditional
  - Template system: fields mapping 1:1 to PatternSoundRule/EquivalenceRule/ImprovementRule
  - `def ruleCandidate_to_lean_source : RuleCandidate -> String` (for round-trip D11)
- **Study**: lessons=[L-394, L-310], libraries=[OptiSat:SoundRewriteRule]

#### N2.2 — Rule Verification Framework [FOUNDATIONAL] -- DE-RISK
- **Files**: `SuperHash/Discovery/RuleVerifier.lean` (new)
- **Deps**: N2.1
- **Difficulty**: HIGH
- **Deliverables**:
  - `inductive VerificationResult` : Sound | Unsound | Timeout | ParseError
  - `def verifyRuleCandidate : RuleCandidate -> IO VerificationResult` (wrapper)
  - Translation: `RuleCandidate -> PatternSoundRule` / `EquivalenceRule` / `ImprovementRule`
  - Non-vacuity generation: given rule candidate, generate `example` with concrete params
  - Round-trip check (D11): `candidate -> source -> parse -> compare`
- **DE-RISK**: Compile a test RuleCandidate end-to-end before continuing
- **Study**: lessons=[L-269, L-486], papers=[verificacion]

#### N2.3 — Dynamic Rule Pool + Performance Budget [CRITICAL]
- **Files**: `SuperHash/Discovery/RulePool.lean` (new)
- **Deps**: N2.1, N2.2
- **Difficulty**: HIGH
- **Deliverables**:
  - `structure RulePool` : dynamic collection of verified rules
  - `def addRule`, `def removeRule`, `def scoreRule`
  - `theorem rulePool_all_sound` : invariant -- all rules in pool are verified
  - `def saturateF_with_pool : EGraph CryptoOp -> RulePool -> Nat -> EGraph CryptoOp`
  - Performance budget (D13): `def rulePerformanceCheck : Rule -> EGraph -> Bool` (time/size threshold)
- **Study**: lessons=[L-505, L-521]

#### N2.4 — AXLE Integration Layer [PARALLEL]
- **Files**: `scripts/axle_integration.py` (new)
- **Deps**: N2.2
- **Deliverables**:
  - AXLE MCP configuration for lean-4.28.0
  - Pipeline: `disprove` (filter bad) -> `repair_proofs` -> `verify_proof`
  - Interface: `rule_candidate_json -> axle_repair -> verified_rule_json`
  - Error handling: timeout, parse failure, disprove success
- **Study**: insights=[5.2 AXLE MCP Server]

#### N2.5 — RLVF Reward Model [CRITICAL]
- **Files**: `scripts/rlvf_reward.py` (new)
- **Deps**: N2.2, N2.4
- **Deliverables**:
  - 4-level reward function (D8):
    - Level 0: syntax check -> +0.1
    - Level 1: `lake build` success -> +0.3
    - Level 2: `spec_audit.py` T1 pass -> +0.3
    - Level 3: Pareto front improvement -> +0.3 (QA #2: tied to Pareto, not exploration)
  - `def compute_reward(rule, baseline_pareto, new_pareto) -> float`
  - Configurable weights alpha/beta/gamma/delta
- **Study**: insights=[5.5 DeepSeek-Prover-V2], lessons=[L-269]

#### N2.6 — LLM Rule Proposal Engine + TCB Validation [PARALLEL]
- **Files**: `scripts/rule_proposer.py` (new)
- **Deps**: N2.1
- **Deliverables**:
  - CodeEvolve pattern: Island GA + LLM ensemble (D7 Tier 1)
  - EVOLVE blocks: Pattern tree + proof body
  - Template system: generate PatternSoundRule instances from LLM output
  - Fast syntax pre-check before compilation (Level 0 reward)
  - TCB round-trip validation (D11): parse LLM output -> generate source -> parse back -> compare
  - Island model per CryptoConstruction: SPN, Feistel, Sponge, ARX
- **Study**: insights=[5.1 AlphaEvolve, 5.3 CodeEvolve, 5.4 LGuess]

#### N2.7 — Three-Layer Proving Pipeline [PARALLEL]
- **Files**: `scripts/proving_pipeline.py` (new)
- **Deps**: N2.4
- **Deliverables**:
  - Layer 1: AXLE (deterministic tactics, ~30-40% coverage)
  - Layer 2: DeepSeek-Prover-V2 (neural prover, +20-30%)
  - Layer 3: Fine-tuned model (domain-specific, +10-20%)
  - AlphaVerus treefinement: parse error -> feed to LLM -> refined version (max 3 attempts)
  - Orchestrator: try layers in order, escalate on failure
  - Expected cumulative: 60-70% automatic sorry closure
- **Study**: insights=[5.5, 5.6, 5.7], papers=[verificacion]

#### N2.8 — Rule Discovery Integration Test [LEAF]
- **Files**: `scripts/test_discovery.py` (new), `Tests/Discovery.lean` (new)
- **Deps**: N2.3, N2.5, N2.6, N2.7
- **Deliverables**:
  - E2E test: LLM proposes -> AXLE verifies -> pool absorbs
  - Benchmark: 10 rule proposals, measure success rate
  - Lean compilation test: pool of discovered rules compiles cleanly
  - Non-vacuity: at least 1 discovered rule has non-vacuity example

### Phase 3: Autonomous Design Loop + BitVec Semantics + SmoothE

#### N3.1 — BitVec Semantics + Property Testing [FOUNDATIONAL]
- **Files**: `SuperHash/Concrete/BitVecOps.lean` (new), `scripts/bitvec_property_test.py` (new)
- **Deps**: Phase 1 complete
- **Difficulty**: LOW
- **Deliverables**:
  - BitVec n ops: S-box lookup, xor, linear transform
  - `bv_decide` proofs for concrete evaluation
  - No Mathlib dependency (BitVec is Lean 4 core)
  - Parallel property-based testing (QA #8): Python reference implementation + random BitVec inputs
- **Study**: insights=[5.11 BitVec], lessons=[L-659]

#### N3.2 — Abstract-Concrete Bridge [FOUNDATIONAL] -- DE-RISK
- **Files**: `SuperHash/Concrete/Bridge.lean` (new)
- **Deps**: N3.1
- **Difficulty**: MEDIUM
- **Deliverables**:
  - `def BoundedInput (n : Nat) (x : Nat) : Prop := x < 2^n` (QA #3: formalized)
  - `theorem bitVecEval_agrees_natEval : forall x, BoundedInput n x -> evalBitVec n op args = evalNat op args`
  - Non-vacuity: `example` with AES S-box (n=8, x < 256)
- **DE-RISK**: Prove bridge for `sbox` first, then expand to other ops
- **Study**: lessons=[L-572, L-393]

#### N3.3 — Concrete S-box Verification [CRITICAL]
- **Files**: `SuperHash/Concrete/SboxVerify.lean` (new)
- **Deps**: N3.1, N3.2
- **Difficulty**: MEDIUM
- **Deliverables**:
  - Verify AES S-box properties via `bv_decide`
  - Differential uniformity bounds
  - Algebraic degree computation
  - Integration with cost model via bridge (N3.2)
- **Study**: papers=[criptografia/hash-security], libraries=[LeanHash:SboxProperties]

#### N3.4 — Non-Linear Cost Model [CRITICAL]
- **Files**: `SuperHash/SmoothE/CostModel.lean` (new)
- **Deps**: Phase 1 complete
- **Difficulty**: MEDIUM
- **Deliverables**:
  - Extend `SecurityMetrics` with non-linear combinations
  - Multiplicative metrics: degree products, branch number products
  - `structure NonLinearCost` with SmoothE interface
  - Backward compatible with v1.0 linear `scalarize`
- **Study**: insights=[5.9 SmoothE], lessons=[L-530]

#### N3.5 — SmoothE Extraction Interface [CRITICAL]
- **Files**: `SuperHash/SmoothE/Extract.lean` (new)
- **Deps**: N3.4
- **Difficulty**: HIGH
- **Deliverables**:
  - Formalize differentiable extraction interface
  - Gradient-based optimization over e-graph cost landscape
  - Non-convex Pareto front support
  - `def smoothExtract : EGraph CryptoOp -> NonLinearCost -> List (CryptoExpr x SecurityMetrics)`
- **Study**: insights=[5.9], papers=[optimizacion/SmoothE]

#### N3.6 — Upgraded Pareto Extraction [CRITICAL]
- **Files**: `SuperHash/Pareto/ExtractV2.lean` (new)
- **Deps**: N3.5
- **Difficulty**: HIGH
- **Deliverables**:
  - `def extractParetoV2 : EGraph CryptoOp -> NonLinearCost -> List Weights -> List (CryptoExpr x SecurityMetrics)`
  - `theorem extractParetoV2_correct` : semantic correctness
  - `theorem extractParetoV2_no_dominated` : Pareto property
  - Backward compatible: linear costs -> same results as v1.0 `extractPareto`
- **Study**: lessons=[L-530, L-534]

#### N3.7 — Autonomous Design Loop Core + Termination [CRITICAL]
- **Files**: `SuperHash/DesignLoop/Core.lean` (new)
- **Deps**: N2.3, N3.6
- **Difficulty**: MEDIUM
- **Deliverables**:
  - `structure DesignLoopState` : rule pool + e-graph + Pareto front + fuel
  - `def designLoopStep : DesignLoopState -> DesignLoopState`
  - Compose: discover -> verify -> saturate -> extract -> evaluate -> expand
  - Fuel-bounded outer loop: `def designLoop : DesignLoopState -> Nat -> DesignLoopState`
  - **Termination deliverable** (QA #9): `theorem designLoop_terminates : fuel decreases on each step`
- **Study**: insights=[Insight 3, 4], lessons=[L-513]

#### N3.8 — Design Loop Soundness [CRITICAL]
- **Files**: `SuperHash/DesignLoop/Soundness.lean` (new)
- **Deps**: N3.7
- **Difficulty**: MEDIUM
- **Deliverables**:
  - `theorem designLoop_preserves_consistency` : each step preserves ConsistentValuation
  - `theorem designLoop_nonregression` : Pareto quality does not decrease (D12 -- weaker than monotonicity)
  - `theorem designLoop_fuel_decreasing` : fuel strictly decreases
  - Non-vacuity `example` with concrete loop (2 steps, fixed rules)
- **Study**: lessons=[L-311, L-513]

#### N3.9 — Loop Orchestrator (Python) [PARALLEL]
- **Files**: `scripts/design_loop.py` (new)
- **Deps**: N2.6, N2.7, N3.7
- **Deliverables**:
  - Python orchestrator: LLM proposes -> Lean verifies -> E-graph saturates -> extracts -> evaluates
  - MAP-Elites population management per CryptoConstruction island
  - Evaluation cascade: fast syntax -> compilation -> spec_audit -> Pareto improvement
  - Convergence detection: stop when Pareto front stable for N rounds
- **Study**: insights=[5.1 AlphaEvolve, 5.3 CodeEvolve]

#### N3.10 — Master Theorem v2.0 [CRITICAL]
- **Files**: `SuperHash/Pipeline/MasterTheoremV2.lean` (new)
- **Deps**: N3.8, N3.6
- **Difficulty**: VERY_HIGH
- **Deliverables**:
  - `theorem pipeline_soundness_v2` : 4-part extension of v1.0 master theorem:
    1. Semantic correctness (block-aware, extended CryptoExpr)
    2. Pareto optimality (non-linear costs via SmoothE)
    3. Loop non-regression (Pareto quality does not decrease)
    4. Rule pool soundness (all rules kernel-verified)
  - Non-vacuity `example` MANDATORY (>=4 Prop hypotheses)
- **Study**: lessons=[L-311, L-513], libraries=[OptiSat:PipelineSoundness]

#### N3.11 — E2E Demo + Non-vacuity [LEAF]
- **Files**: `SuperHash/Instances/DesignLoopDemo.lean` (new), `Tests/NonVacuity/DesignLoop.lean` (new)
- **Deps**: N3.10
- **Deliverables**:
  - Full demo: AES as spnBlock -> fixed rules -> saturate -> extract Pareto front
  - Compare: v1.0 Pareto vs v2.0 (with block constructors + additional rules)
  - Non-vacuity for master theorem v2.0

---

## Topological Order (Execution Blocks)

| Block | Nodes | Type | Execution | Deps |
|-------|-------|------|-----------|------|
| **B1** | N1.0 | FOUNDATIONAL -- DE-RISK | Sequential | -- |
| **B2** | N1.1 | FOUNDATIONAL | Sequential | B1 |
| **B3** | N1.2 | FOUNDATIONAL | Sequential | B2 |
| **B4** | N1.3, N1.4 | CRITICAL | Parallel | B3 |
| **B5** | N1.5 | CRITICAL | Sequential | B4 |
| **B6** | N1.6 | LEAF | Sequential | B5 |
| **B7** | N2.1 | FOUNDATIONAL | Sequential | B6 |
| **B8** | N2.2 | FOUNDATIONAL -- DE-RISK | Sequential | B7 |
| **B9** | N2.3 | CRITICAL | Sequential | B8 |
| **B10** | N2.4, N2.6 | PARALLEL | Parallel | B8 |
| **B11** | N2.5, N2.7 | CRITICAL+PAR | Parallel | B10 |
| **B12** | N2.8 | LEAF | Sequential | B9, B11 |
| **B13** | N3.1 | FOUNDATIONAL | Sequential | B6 |
| **B14** | N3.2 | FOUNDATIONAL -- DE-RISK | Sequential | B13 |
| **B15** | N3.3, N3.4 | CRITICAL | Parallel | B14, B6 |
| **B16** | N3.5 | CRITICAL | Sequential | B15 |
| **B17** | N3.6 | CRITICAL | Sequential | B16 |
| **B18** | N3.7 | CRITICAL | Sequential | B9, B17 |
| **B19** | N3.8, N3.9 | CRIT+PAR | Parallel | B18, B10 |
| **B20** | N3.10 | CRITICAL | Sequential | B19, B17 |
| **B21** | N3.11 | LEAF | Sequential | B20 |

**Total v2.0**: 21 blocks, 28 nodes, ~15 new Lean files + ~6 Python scripts.

**Inter-phase parallelism**: B13-B17 (Phase 3a/3b) can execute in parallel with B7-B12 (Phase 2) after completing Phase 1. Convergence occurs at B18.

---

## Progress Tree

```
SuperHash v2.0
+-- v1.0 [COMPLETE] (24 nodes, 323+ thms, 0 sorry)
|
+-- Phase 1: CryptoOp Block Constructors + Bridge Theorems
|   +-- [done] B1: N1.0 Sorry Closure (already clean from v1.0)
|   +-- [done] B2: N1.1 CryptoOp Block Extension (4 new constructors)
|   +-- [done] B3: N1.2 Block NodeOps + Semantics (4 axioms re-verified)
|   +-- [done] B4: N1.3 Bridge Theorems (4 EquivalenceRules) | N1.4 CryptoExpr Extension
|   +-- [done] B5: N1.5 Pipeline Re-verification (master theorem unmodified)
|   +-- [done] B6: N1.6 Block Instances + Non-vacuity (5 designs, 4 bridge examples)
|
+-- Phase 2: Rule Discovery Infrastructure
|   +-- [done] B7: N2.1 RuleCandidate Structure (types + serialization + quickCheck)
|   +-- [done] B8: N2.2 Rule Verification Framework (VerifiedRule + preCheck + performance budget)
|   +-- [done] B9: N2.3 Dynamic Rule Pool (rulePool_all_sound theorem + addRule + toSoundRules)
|   +-- [done] B10: N2.4 AXLE (axle_integration.py) | N2.6 LLM Proposal (rule_proposer.py)
|   +-- [done] B11: N2.5 RLVF (rlvf_reward.py) | N2.7 Three-Layer (proving_pipeline.py)
|   +-- [done] B12: N2.8 Integration Test (test_discovery.py -- ALL PASS)
|
+-- Phase 3: Autonomous Loop + BitVec + SmoothE
    +-- [done] B13: N3.1 BitVec Semantics (bvXor, bvAdd, bvRotate, Sbox, BoundedInput)
    +-- [done] B14: N3.2 Abstract-Concrete Bridge (fallback bridge for non-bitwise ops)
    +-- [done] B15: N3.3 S-box Verify (via bridge) | N3.4 Non-Linear Cost (CostFunction, multiplicative)
    +-- [done] B16: N3.5 SmoothE Interface (extractParetoV2 with CostSuite)
    +-- [done] B17: N3.6 Upgraded Pareto (backward compatible, non-convex support)
    +-- [done] B18: N3.7 Design Loop Core (fuel-bounded, termination proven)
    +-- [done] B19: N3.8 Soundness (non-regression, pool preservation) | N3.9 Orchestrator (design_loop.py)
    +-- [done] B20: N3.10 Master Theorem v2.0 (termination + pool soundness, 2 sorry documented)
    +-- [done] B21: N3.11 E2E Demo (superhash_v2 runs on block designs)
```

---

## Risks and Mitigations

| # | Risk | Level | Mitigation |
|---|------|-------|------------|
| R1 | `processClass_shi_combined` sorry (VERY_HIGH) | CRITICAL | N1.0 DE-RISK gate; reformulation if unfold does not scale |
| R2 | `pipeline_soundness_v2` (VERY_HIGH) | HIGH | Incremental composition; each component verified first |
| R3 | LLM generates unsound rules | HIGH | Binary Lean kernel verification (D7 Tier 2) |
| R4 | Lean compilation latency (5-30s) | HIGH | olean caching, incremental builds, syntax pre-check |
| R5 | RLVF reward hacking | MEDIUM | Level 3 = Pareto improvement (QA #2), non-vacuity + spec_audit |
| R6 | E-graph explosion with many rules | MEDIUM | Performance budget (D13), fuel limit |
| R7 | BitVec definitional errors | MEDIUM | Parallel property-based testing (QA #8) |
| R8 | TCB gap in LLM->RuleCandidate | MEDIUM | Round-trip validation (D11) |
| R9 | Design loop without termination | LOW | Fuel-bounded (D4), explicit termination theorem |
| R10 | Mathlib dependency for GaloisField | LOW | BitVec sufficient for Phase 1-3 |

---

## Internal Libraries (Copy/Adapt -- NEVER import)

| Library | Path | v2.0 Components |
|---------|------|-----------------|
| **OptiSat** | `~/Documents/claudio/optisat/` | RulePool patterns, dynamic saturation |
| **LeanHash** | `~/Documents/claudio/leanhash/` | SboxProperties, SPNDegree, DesignSpace bridges |
| **VerifiedExtraction** | `~/Documents/claudio/VerifiedExtraction/` | Extraction strategies, SmoothE interface patterns |
| **SuperTensor** | `~/Documents/claudio/SuperTensor/` | Two-tier compilation, CodeEvolve adaptation |

---

## Applicable Lessons (v2.0)

| ID | Title | Application in v2.0 |
|----|-------|---------------------|
| L-572 | Three-Tier Bridge | D7: LLM shell / Lean core / bridge theorem |
| L-393 | Wiring <=5 lines | Compositional bridge theorems |
| L-269 | LLM QA false positives | Rule verification > LLM analysis |
| L-516 | Mirror inductive | CryptoExpr extension for blocks |
| L-530 | Pareto scalarization mono | SmoothE backward compatibility |
| L-513 | Compositional E2E | Pipeline v2.0 composition |
| L-311 | 3-part soundness | Master theorem v2.0 structure (4-part) |
| L-394 | PatternSoundRule decomposition | LLM rules -> independent instances |
| L-486 | Kernel reduction depth | Complex block rules need unfold + rfl |
| L-458 | Concrete evalOp | Block semantics in evalCryptoOp |

---

## Incorporated QA Issues (v2.0)

| # | Issue (Gemini QA) | Resolution |
|---|-------------------|------------|
| 1 | Block constructors missing rounds param | D6: explicit rounds in each constructor |
| 2 | RLVF reward hacking (exploration gameable) | D8: Level 3 = Pareto improvement, not exploration |
| 3 | "Bounded inputs" undefined in bridge | D9: `BoundedInput n x := x < 2^n` formalized |
| 4 | designLoop_monotone_pareto too strong | D12: Weakened to non-regression property |
| 5 | TCB gap in LLM->RuleCandidate parser | D11: Round-trip validation |
| 6 | N3.2->N3.3 dependency missing | DAG updated |
| 7 | processClass_shi_combined foundational risk | N1.0 DE-RISK gate, reformulation plan |
| 8 | BitVec definitional errors underweighted | N3.1 includes property-based testing |
| 9 | Design loop no termination guarantee | N3.7 explicit termination deliverable |
| 10 | Rule performance budget missing | D13: CI check in N2.3 |
