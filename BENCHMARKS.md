# SuperHash v2.0 - Verification Criteria (Benchmark QA)

**Version:** v2.0 (Planning)
**Generated:** 2026-03-13
**Status:** v1.0 criteria below (historical) + v2.0 criteria appended
**Base**: v1.0 complete (323+ thms, 0 sorry, 0 axioms)

---

## Overview

This document defines **exhaustive verification criteria** for SuperHash v1.0, a formally verified Lean 4 framework for automated cryptographic hash function design via E-graphs. The criteria are structured as **formal proof obligations** rather than implementation checklists, reflecting the nature of pure verification projects.

**Project Context:**
- **Domain:** Lean 4 without Mathlib
- **Architecture:** 6 phases, 24 nodes
- **Node Types:** FUNDACIONAL, CRÍTICO, PARALELO, HOJA
- **Objective:** Zero-sorry, axiom-free, compositional soundness from primitives to end-to-end pipeline

---

## A. Mandatory Mechanical Checks (Global)

These checks apply to **every phase** and **every commit** before closing any block.

| Check ID | Criterion | Verification Method |
|----------|-----------|---------------------|
| **M-1** | **Zero Sorry** | `rg --count-matches "sorry" SuperHash/ == 0` |
| **M-2** | **Axiom-Free** | No custom axioms introduced (verify with `#print axioms` on all theorems) |
| **M-3** | **Clean Build** | `lake build` completes without errors or warnings |
| **M-4** | **Termination Proofs** | All recursive functions accepted by Lean without `partial` or `unsafe` |
| **M-5** | **No Identity Passes** | No pipeline field uses `:= id` or `fun x => x` without PENDIENTE tag in DAG |
| **M-6** | **DecidableEq Coverage** | Every custom inductive type has `DecidableEq` instance |

**Failure Mode:** Any M-1 through M-6 failure blocks phase completion.

---

## B. Criteria by Node Type

### 1. FUNDACIONAL Nodes

**Covered Nodes:**
- `CryptoOp` inductive type
- `DesignParams` structure
- `NodeOps` typeclass
- `SoundCryptoRule` structure
- Scalarization definitions
- Master Theorem statement

#### Proof Obligations

| Obligation ID | Theorem Statement | Rationale |
|--------------|-------------------|-----------|
| **F-1** | `∀ (op : CryptoOp), DecidableEq op` | Decidability required for E-graph union-find |
| **F-2** | `∀ (p : DesignParams), DecidableEq p` | Decidability for parameter comparison |
| **F-3** | Algebraic laws for `CryptoOp` operations (if applicable) | Example: `∀ x y, xor x y = xor y x` (commutativity) |
| **F-4** | `NodeOps` typeclass laws defined and stated | Example: `∀ (instance : NodeOps T), op_preserves_semantics instance` |
| **F-5** | `∀ (instance : NodeOps T), instance_obeys_laws instance` | Proof that each concrete instance satisfies F-4 laws |
| **F-6** | `∀ (r : SoundCryptoRule), semantically_equal r.lhs r.rhs` | Central soundness property of rewrite rules |
| **F-7** | Master Theorem formally stated with explicit preconditions | Must be a concrete `theorem` declaration, not a comment |

#### Stress Tests

| Test ID | Scenario | Expected Behavior |
|---------|----------|-------------------|
| **SF-1** | `CryptoOp` with 0 arguments (nullary op) | Type system accepts, operations defined |
| **SF-2** | `CryptoOp` with maximum arity (e.g., 8 args) | No stack overflow, decidable operations |
| **SF-3** | `DesignParams` with all-zero fields | Valid params, no division by zero in cost functions |
| **SF-4** | `NodeOps` instance for degenerate type (e.g., `Unit`) | Compiles, laws trivially satisfied |

#### Architectural Coherence

- **AC-F1:** Every field in `DesignParams` must be read by at least one cost function or constraint predicate
- **AC-F2:** Every `CryptoOp` constructor must appear in at least one concrete rewrite rule
- **AC-F3:** The `NodeOps` typeclass must export operations used by the E-graph engine (lookup, apply, hash)

---

### 2. CRÍTICO Nodes

**Covered Nodes:**
- E-Graph Core (EClass, union-find)
- ConsistentValuation
- Concrete Rewrite Rules (8-12 rules)
- Rule Preservation Bridge
- `SaturateF` (saturation function)
- Stage Soundness theorems
- `ExtractPareto`
- Pareto Soundness
- Pipeline Composition

#### Proof Obligations

| Obligation ID | Theorem Statement | Rationale |
|--------------|-------------------|-----------|
| **C-1** | `∀ g fuel, ∃ g', saturateF g fuel = g'` | **Termination:** Saturation always terminates |
| **C-2** | `∀ g, saturateF g (max_fuel g) = saturateF (saturateF g (max_fuel g)) (max_fuel g)` | **Fixpoint:** Saturation reaches a fixpoint |
| **C-3** | `∀ g n1 n2, (find g n1) = (find g n2) → semantically_equal n1 n2` | **Soundness:** Union-find preserves semantic equality |
| **C-4** | `∀ g n1 n2, semantically_equal n1 n2 → ∃ g', (find (saturateF g max_fuel) n1) = (find g' n2)` | **Completeness:** Saturation discovers all equalities (relative to rule set) |
| **C-5** | `∀ (v : Valuation) (g : EGraph), consistent v g → (∀ n1 n2, find g n1 = find g n2 → v n1 = v n2)` | **ConsistentValuation:** Semantic interpretation respects E-class equivalence |
| **C-6** | `∀ (r : ConcreteRule), ∀ g n, r.applies g n → semantically_equal (r.lhs_pattern n) (r.rhs_pattern n)` | **Rule Soundness:** Each concrete rule preserves semantics |
| **C-7** | `∀ (stage_i : PipelineStage), ∀ x, P_{i-1} x → P_i (stage_i.transform x)` | **Stage Soundness:** Each pipeline stage preserves invariants |
| **C-8** | `∀ g, let S := extractPareto g; ∀ s ∈ S, ¬(∃ s' ∈ S, s' ≠ s ∧ dominates s' s)` | **Pareto Soundness:** Extracted set contains no dominated elements |
| **C-9** | `∀ g, let S := extractPareto g; ∀ n ∈ (nodes g), is_pareto_optimal n g → (∃ s ∈ S, semantically_equal n s)` | **Pareto Completeness:** All Pareto-optimal nodes have a representative in extracted set |
| **C-10** | `∀ (d : DesignParams), let P := full_pipeline d; ∀ p ∈ P, is_valid_hash_candidate p ∧ is_pareto_optimal_wrt_d p d` | **End-to-End Soundness:** Pipeline composition preserves validity and Pareto-optimality |

#### Stress Tests

| Test ID | Scenario | Expected Behavior |
|---------|----------|-------------------|
| **SC-1** | Empty E-graph (0 nodes) | Saturation terminates immediately, `extractPareto` returns `[]` |
| **SC-2** | Single-node E-graph | Saturation terminates, node is trivially Pareto-optimal |
| **SC-3** | E-graph with self-loops (n1 → n1) | Union-find handles cycles, saturation terminates |
| **SC-4** | Zero fuel (`saturateF g 0`) | Returns input graph unchanged (identity) |
| **SC-5** | Fuel = 1 | Applies exactly one rewrite round |
| **SC-6** | Maximum arity nodes (e.g., 8-input XOR) | Pattern matching works, no stack overflow |
| **SC-7** | Degenerate `DesignParams` (all constraints maxed out) | Pipeline returns empty Pareto set (valid behavior) |
| **SC-8** | Rule with contradictory preconditions | Rule never applies (verified via non-vacuity test showing `¬∃ g n, rule.applies g n`) |

#### Edge Cases

| Case ID | Scenario | Required Behavior |
|---------|----------|-------------------|
| **EC-1** | Two nodes with identical costs but different semantics | Both appear in Pareto set (no semantic dominance) |
| **EC-2** | Graph where all nodes are semantically equivalent | Pareto set contains exactly one representative |
| **EC-3** | Rule application creates a cycle in E-graph structure | Union-find correctly merges classes, no infinite loop |
| **EC-4** | Extracting from a graph mid-saturation (not at fixpoint) | Extraction succeeds, but Pareto set may be incomplete (relative to full saturation) |

#### Proof Quality Anti-Patterns (Prohibited)

| Anti-Pattern | Why Prohibited | Detection |
|--------------|----------------|-----------|
| **Excessive `native_decide`** | Masks proof structure, fails on abstract types | Manual review: flag `native_decide` in theorems with >3 hypotheses |
| **`simp [*]` without specific lemmas** | Non-reproducible, fragile to lemma additions | CI check: reject `simp [*]` in pipeline theorems |
| **`decide` on >256 cases** | Compile-time explosion, unreadable proof | Review: flag `decide` calls on large inductives |
| **Theorems with 0 hypotheses proven via `trivial`** | Likely a tautology (`True`, `P → P`) | Audit: flag theorems with conclusion = `True` or `⊤` |

#### Architectural Coherence

- **AC-C1:** Every `ConcreteRule` must be registered in the rule database used by `saturateF`
- **AC-C2:** The Rule Preservation Bridge must have a theorem proving `∀ r, interp_simplified r = interp_complex r` for each rule
- **AC-C3:** Each pipeline stage must have a consumer (either the next stage or the final output aggregator)
- **AC-C4:** The `ExtractPareto` function must be called exactly once in the pipeline (no redundant extractions)

---

### 3. PARALELO Nodes

**Covered Nodes:**
- Pareto Dominance relation
- Concrete Instances (for typeclasses)
- `ComputeCostsF` function
- `ExtractF` (greedy extraction)
- Bool-Prop Bridge

#### Proof Obligations

| Obligation ID | Theorem Statement | Rationale |
|--------------|-------------------|-----------|
| **P-1** | `∀ x, ¬(dominates x x)` | **Irreflexivity:** Pareto dominance is irreflexive |
| **P-2** | `∀ x y z, dominates x y → dominates y z → dominates x z` | **Transitivity:** Pareto dominance is transitive |
| **P-3** | `∀ (n1 n2 : Node) (r : ImprovementRule), rewrites r n1 n2 → cost n2 ≤ cost n1` | **Cost Consistency:** Improvement rules reduce cost |
| **P-4** | `∀ (e : BoolExpr), eval_bool e = true ↔ InterpProp e` | **Bool-Prop Equivalence:** Boolean and propositional semantics coincide |
| **P-5** | `∀ (instance : MyTypeclass T), DecidableEq T` | **Instance Coherence:** All typeclass instances provide decidability |
| **P-6** | `∀ g, extractF_greedy g ⊆ nodes g ∧ (∀ n ∈ extractF_greedy g, ¬∃ n' ∈ extractF_greedy g, dominates n' n)` | **Greedy Extraction Soundness:** Extracted nodes are Pareto-optimal within the extraction |

#### Stress Tests

| Test ID | Scenario | Expected Behavior |
|---------|----------|-------------------|
| **SP-1** | Two nodes with identical costs across all dimensions | Neither dominates the other (both in Pareto set) |
| **SP-2** | Node with one cost dimension = 0 | Cost computation handles zero gracefully |
| **SP-3** | `ComputeCostsF` on empty graph | Returns empty cost map |
| **SP-4** | `ExtractF` with greedy heuristic on graph with 1000 nodes | Terminates in reasonable time, returns valid subset |
| **SP-5** | Bool-Prop bridge on formula with 100 variables | `eval_bool` and `InterpProp` agree (test via `decide`) |

#### Architectural Coherence

- **AC-P1:** Every cost dimension defined in `DesignParams` must be computed by `ComputeCostsF`
- **AC-P2:** The Pareto dominance relation must be used by `ExtractPareto` (not redefined)
- **AC-P3:** The Bool-Prop bridge must have a consumer theorem that relies on the equivalence (not orphaned)

---

### 4. HOJA Nodes

**Covered Nodes:**
- Smoke Tests
- Rule Non-vacuity proofs
- Evaluation instances (e.g., `ToString`, `Repr`)
- E2E Non-vacuity examples

#### Proof Obligations

| Obligation ID | Theorem Statement | Rationale |
|--------------|-------------------|-----------|
| **H-1** | `∀ (r : ConcreteRule), ∃ g n, r.applies g n` | **Rule Non-vacuity:** Each rule is applicable to at least one graph/node pair |
| **H-2** | `∃ (d : DesignParams), let P := full_pipeline d; P ≠ [] ∧ P.length > 1` | **E2E Non-vacuity:** Pipeline produces non-trivial output for some input |
| **H-3** | `∀ (instance : ToString T), ∀ x, (toString x).length > 0` | **Instance Sanity:** `ToString` instances produce non-empty strings |
| **H-4** | Smoke tests for each major component (no proof obligation, but must compile and run) | **Basic Execution:** Verify that example inputs run without runtime errors |

#### Stress Tests

| Test ID | Scenario | Expected Behavior |
|---------|----------|-------------------|
| **SH-1** | Non-vacuity example with minimal graph (2 nodes, 1 edge) | Rule applies, example compiles |
| **SH-2** | E2E example with `DesignParams` at extremes (min rounds, max cost threshold) | Pipeline runs, produces output |
| **SH-3** | `ToString` instance on deeply nested structure (depth 10) | No stack overflow, readable output |

#### Architectural Coherence

- **AC-H1:** Every `ConcreteRule` must have a corresponding non-vacuity `example` in `Tests/NonVacuity.lean`
- **AC-H2:** The E2E non-vacuity example must use the actual `full_pipeline` function (not a mock)
- **AC-H3:** Smoke tests must cover at least one example per pipeline stage

---

## C. Cross-Cutting Concerns

These criteria apply across **all node types** and verify architectural properties.

### 1. Wiring Integrity

| Check ID | Criterion | Verification Method |
|----------|-----------|---------------------|
| **W-1** | **No Module Islands** | Every module (`.lean` file) must be imported by at least one other module (or be the root) |
| **W-2** | **No Dead Fields** | Every field in every `structure` must be read by at least one function or theorem |
| **W-3** | **No Phantom Opens** | Every `open Namespace` must be followed by a use of a declaration from that namespace |
| **W-4** | **Bridge Theorems Exist** | For every simplification/abstraction (e.g., `simple_cost` vs `full_cost`), there must be a bridge theorem proving equivalence or refinement |
| **W-5** | **Consumer Verification** | Every exported definition must be used by at least one downstream module (not just re-exported) |

**Detection:** Run wiring audit script after each phase:
```bash
python3 ~/.claude/skills/plan-project/scripts/wiring_audit.py --strict SuperHash/
```

### 2. Pipeline Integrity

| Check ID | Criterion | Verification Method |
|----------|-----------|---------------------|
| **PI-1** | **Correct Order** | Pipeline stages must execute in order: `saturate → costs → extract → pareto` |
| **PI-2** | **No Skipped Stages** | Every stage defined in the architecture must appear in `full_pipeline` |
| **PI-3** | **Type Compatibility** | Output type of stage `i` must match input type of stage `i+1` |
| **PI-4** | **Soundness Chain** | There must be a theorem proving end-to-end soundness by composing individual stage soundness theorems |

**Detection:** Manual review of `SuperHash/Pipeline.lean` + verify existence of `pipeline_composition_soundness` theorem.

### 3. Non-Vacuity Coverage

| Check ID | Criterion | Verification Method |
|----------|-----------|---------------------|
| **NV-1** | **Theorems with ≥3 Prop Hypotheses** | Must have a corresponding `example` instantiating all hypotheses |
| **NV-2** | **Compositional Chains** | Root theorem of a soundness chain must have an end-to-end `example` |
| **NV-3** | **Examples Compile** | All non-vacuity examples must compile without `sorry` |
| **NV-4** | **Examples Use `native_decide` or Explicit Construction** | No `sorry` or `admit` in hypothesis witnesses |

**Detection:** Run spec audit:
```bash
python3 ~/.claude/skills/plan-project/scripts/spec_audit.py --pipeline-only SuperHash/
```
Flag **T4-NO-WITNESS** findings.

### 4. Identity Pass Prohibition

| Check ID | Criterion | Verification Method |
|----------|-----------|---------------------|
| **IP-1** | **No `:= id` in Pipeline** | No pipeline structure field may use `:= id` unless tagged PENDIENTE in ARCHITECTURE.md |
| **IP-2** | **No `fun x => x` in Pipeline** | No pipeline structure field may use `fun x => x` unless tagged PENDIENTE |
| **IP-3** | **Documented Debt** | Every PENDIENTE identity pass must have a GitHub issue or DAG node tracking its replacement |

**Detection:** Manual code review + grep for `:= id` and `fun x => x` in pipeline files.

### 5. Specification Hygiene

| Check ID | Criterion | Verification Method |
|----------|-----------|---------------------|
| **SH-1** | **No Vacuous Theorems** | No `theorem ... : True` or `theorem ... : ⊤` |
| **SH-2** | **No Universal Underscores** | No theorems with all parameters prefixed with `_` (indicates unused hypotheses) |
| **SH-3** | **Directional Correctness** | Theorems named `*_sound` must have conclusion with `=`, `↔`, or `→` |
| **SH-4** | **Hypothesis Limit** | Pipeline theorems should have ≤8 hypotheses (extract complex conditions as definitions) |
| **SH-5** | **Smoke Tests for Satisfiability** | Every pipeline theorem must have a `#eval` or `example` below it verifying hypotheses are satisfiable |

**Detection:** Run spec audit:
```bash
python3 ~/.claude/skills/plan-project/scripts/spec_audit.py --strict SuperHash/
```
Address all **T1-VACUOUS-TRUE**, **T2-UNUSED-HYPS**, **T3-WRONG-DIRECTION** findings.

---

## D. Benchmark Execution Protocol

### Phase Completion Checklist

Before closing any phase:

1. **Run Mechanical Checks:**
   ```bash
   lake build                          # M-3: Clean build
   rg --count-matches "sorry" SuperHash/  # M-1: Zero sorry
   python3 ~/.claude/skills/plan-project/scripts/spec_audit.py --strict SuperHash/  # M-2, SH-1 to SH-5
   ```

2. **Run Architectural Audits:**
   ```bash
   python3 ~/.claude/skills/plan-project/scripts/wiring_audit.py --strict SuperHash/  # W-1 to W-5
   ```

3. **Verify Node-Specific Obligations:**
   - Manually review proof obligations table for current phase
   - For FUNDACIONAL nodes: verify F-1 to F-7
   - For CRÍTICO nodes: verify C-1 to C-10
   - For PARALELO nodes: verify P-1 to P-6
   - For HOJA nodes: verify H-1 to H-4

4. **Execute Stress Tests:**
   - Run all tests in `Tests/Stress/` directory for current phase
   - Verify expected behaviors match criteria tables

5. **Cross-Cutting Verification:**
   - Check pipeline integrity (PI-1 to PI-4)
   - Verify non-vacuity coverage (NV-1 to NV-4)
   - Confirm no identity passes (IP-1 to IP-3)

6. **Document Results:**
   - Update this file with pass/fail status for each criterion
   - Tag commit with phase version (e.g., `v1.0-fase1`)
   - Extract lessons via `close_block.py --lessons`

### Failure Resolution

If any criterion fails:
- **BLOCK:** Do not proceed to next phase
- **DOCUMENT:** Add failure details to `ARCHITECTURE.md` under current node
- **PLAN:** Create a remediation task in the DAG
- **RE-TEST:** After fix, re-run full benchmark suite for the phase

---

## E. Results Log (To Be Populated During Implementation)

### Phase 1: Foundations (Pending)
- **Status:** Not started
- **Obligations:** F-1 to F-7
- **Results:** TBD

### Phase 2: E-Graph Core (Pending)
- **Status:** Not started
- **Obligations:** C-1 to C-5
- **Results:** TBD

### Phase 3: Rewrite Rules (Pending)
- **Status:** Not started
- **Obligations:** C-6, H-1
- **Results:** TBD

### Phase 4: Pipeline Stages (Pending)
- **Status:** Not started
- **Obligations:** C-7 to C-10, P-1 to P-6
- **Results:** TBD

### Phase 5: Integration (Pending)
- **Status:** Not started
- **Obligations:** W-1 to W-5, PI-1 to PI-4
- **Results:** TBD

### Phase 6: Validation (Pending)
- **Status:** Not started
- **Obligations:** NV-1 to NV-4, H-2, H-4
- **Results:** TBD

---

## F. Acceptance Criteria for v1.0 Release

SuperHash v1.0 is **ready for release** when:

1. ✅ All mechanical checks (M-1 to M-6) pass
2. ✅ All FUNDACIONAL obligations (F-1 to F-7) proven
3. ✅ All CRÍTICO obligations (C-1 to C-10) proven
4. ✅ All PARALELO obligations (P-1 to P-6) proven
5. ✅ All HOJA obligations (H-1 to H-4) satisfied
6. ✅ All cross-cutting checks (W-1 to W-5, PI-1 to PI-4, NV-1 to NV-4, IP-1 to IP-3, SH-1 to SH-5) pass
7. ✅ End-to-end example in `Tests/NonVacuity.lean` compiles and runs
8. ✅ Benchmark results documented in section E above
9. ✅ All phases tagged with version numbers
10. ✅ `ARCHITECTURE.md` reflects final state (no PENDIENTE nodes with identity passes)

**Final Verification Command:**
```bash
lake build && \
python3 ~/.claude/skills/plan-project/scripts/spec_audit.py --strict SuperHash/ && \
python3 ~/.claude/skills/plan-project/scripts/wiring_audit.py --strict SuperHash/ && \
rg --count-matches "sorry" SuperHash/ | grep -q "^0$" && \
echo "✅ SuperHash v1.0 VERIFIED"
```

---

## G. Gemini 2.5 Pro QA Review Summary

**Round 1 Assessment (2026-03-13):**

**Strengths Identified:**
- Comprehensive enumeration of components and node types
- Relevant stress tests and edge cases for Lean 4 environment
- Strong grasp of project structure

**Critical Improvements Implemented:**
1. **Reframed as Formal Proof Obligations:** Shifted from implementation checklist to theorem-based verification criteria
2. **Added Mathematical Rigor:** Every criterion now expressed as a concrete theorem statement (e.g., `∀ g fuel, ∃ g', saturateF g fuel = g'`)
3. **Foundational Guarantees:** Added decidability, typeclass laws, and termination proofs as mandatory
4. **Algorithmic Properties:** Included termination, fixpoint, soundness, and completeness proofs for E-graph saturation
5. **Typeclass Laws:** Explicitly require definition and proof of laws for all typeclasses

**Key Additions from QA:**
- C-1 to C-4: E-graph correctness properties (termination, fixpoint, soundness, completeness)
- F-3 to F-5: Algebraic laws and typeclass coherence
- P-1 to P-2: Pareto dominance order properties
- NV-1 to NV-4: Comprehensive non-vacuity coverage
- SH-1 to SH-5: Specification hygiene rules

**Outcome:** Criteria elevated from testing plan to formal verification standard, suitable for a Lean 4 pure proof project.

---

**Last Updated:** 2026-03-13
**Next Review:** After Phase 1 completion

## Current Results

### Stage Soundness (v1.0.0)

**Closed**: 2026-03-13 | **Status**: PASS

#### 1. What is tested and why

Nodes covered: N4.4 Stage Soundness Composition.

#### 2. Performance

| Metric | Target | Actual | Status |
|--------|--------|--------|--------|
| LOC | — | 0 | — |
| Theorems | — | 0 | — |
| Lemmas | — | 0 | — |
| Defs | — | 0 | — |
| Sorry count | 0 | 0 | PASS |

#### 3. Acceptability Analysis

- **Acceptable**: Meets minimum criteria (zero sorry, compiles)

#### 4. Bugs, Warnings, Sorries

| Item | Location | Cause | Affected Nodes | Mitigation |
|------|----------|-------|----------------|------------|
| (none) | — | — | — | — |

### Scalarization + Bool-Prop Bridge (v1.0.0)

**Closed**: 2026-03-13 | **Status**: PASS

#### 1. What is tested and why

Nodes covered: N5.1 Scalarization + Monotonicity, N5.2 Bool-Prop Bridge.

#### 2. Performance

| Metric | Target | Actual | Status |
|--------|--------|--------|--------|
| LOC | — | 0 | — |
| Theorems | — | 0 | — |
| Lemmas | — | 0 | — |
| Defs | — | 0 | — |
| Sorry count | 0 | 0 | PASS |

#### 3. Acceptability Analysis

- **Acceptable**: Meets minimum criteria (zero sorry, compiles)

#### 4. Bugs, Warnings, Sorries

| Item | Location | Cause | Affected Nodes | Mitigation |
|------|----------|-------|----------------|------------|
| (none) | — | — | — | — |

### ExtractPareto (v1.0.0)

**Closed**: 2026-03-13 | **Status**: PASS

#### 1. What is tested and why

Nodes covered: N5.3 ExtractPareto.

#### 2. Performance

| Metric | Target | Actual | Status |
|--------|--------|--------|--------|
| LOC | — | 0 | — |
| Theorems | — | 0 | — |
| Lemmas | — | 0 | — |
| Defs | — | 0 | — |
| Sorry count | 0 | 0 | PASS |

#### 3. Acceptability Analysis

- **Acceptable**: Meets minimum criteria (zero sorry, compiles)

#### 4. Bugs, Warnings, Sorries

| Item | Location | Cause | Affected Nodes | Mitigation |
|------|----------|-------|----------------|------------|
| (none) | — | — | — | — |

### Pareto Soundness (v1.0.0)

**Closed**: 2026-03-13 | **Status**: PASS

#### 1. What is tested and why

Nodes covered: N5.4 Pareto Soundness.

#### 2. Performance

| Metric | Target | Actual | Status |
|--------|--------|--------|--------|
| LOC | — | 0 | — |
| Theorems | — | 0 | — |
| Lemmas | — | 0 | — |
| Defs | — | 0 | — |
| Sorry count | 0 | 0 | PASS |

#### 3. Acceptability Analysis

- **Acceptable**: Meets minimum criteria (zero sorry, compiles)

#### 4. Bugs, Warnings, Sorries

| Item | Location | Cause | Affected Nodes | Mitigation |
|------|----------|-------|----------------|------------|
| (none) | — | — | — | — |

### Pipeline Composition (v1.0.0)

**Closed**: 2026-03-13 | **Status**: PASS

#### 1. What is tested and why

Nodes covered: N6.1 Pipeline Composition.

#### 2. Performance

| Metric | Target | Actual | Status |
|--------|--------|--------|--------|
| LOC | — | 0 | — |
| Theorems | — | 0 | — |
| Lemmas | — | 0 | — |
| Defs | — | 0 | — |
| Sorry count | 0 | 0 | PASS |

#### 3. Acceptability Analysis

- **Acceptable**: Meets minimum criteria (zero sorry, compiles)

#### 4. Bugs, Warnings, Sorries

| Item | Location | Cause | Affected Nodes | Mitigation |
|------|----------|-------|----------------|------------|
| (none) | — | — | — | — |

### Master Soundness Theorem (v1.0.0)

**Closed**: 2026-03-13 | **Status**: PASS

#### 1. What is tested and why

Nodes covered: N6.2 Master Soundness Theorem.

#### 2. Performance

| Metric | Target | Actual | Status |
|--------|--------|--------|--------|
| LOC | — | 0 | — |
| Theorems | — | 0 | — |
| Lemmas | — | 0 | — |
| Defs | — | 0 | — |
| Sorry count | 0 | 0 | PASS |

#### 3. Acceptability Analysis

- **Acceptable**: Meets minimum criteria (zero sorry, compiles)

#### 4. Bugs, Warnings, Sorries

| Item | Location | Cause | Affected Nodes | Mitigation |
|------|----------|-------|----------------|------------|
| (none) | — | — | — | — |

### Evaluation + E2E Non-vacuity (v1.0.0)

**Closed**: 2026-03-13 | **Status**: PASS

#### 1. What is tested and why

Nodes covered: N6.3 Evaluation Instances, N6.4 Non-vacuity E2E.

#### 2. Performance

| Metric | Target | Actual | Status |
|--------|--------|--------|--------|
| LOC | — | 0 | — |
| Theorems | — | 0 | — |
| Lemmas | — | 0 | — |
| Defs | — | 0 | — |
| Sorry count | 0 | 0 | PASS |

#### 3. Acceptability Analysis

- **Acceptable**: Meets minimum criteria (zero sorry, compiles)

#### 4. Bugs, Warnings, Sorries

| Item | Location | Cause | Affected Nodes | Mitigation |
|------|----------|-------|----------------|------------|
| (none) | — | — | — | — |

---
---

# v2.0 Verification Criteria

**Generated:** 2026-03-13 via Gemini 2.5 Pro QA (2 rounds)
**Scope**: 3 phases, 28 nodes, 21 blocks

## V2-A. Global Mechanical Checks

| Check ID | Criterion | Verification |
|----------|-----------|-------------|
| **V2-M1** | All v1.0 checks (M-1 to M-6) still pass | Regression guard |
| **V2-M2** | No `sorry` in Discovery/ or DesignLoop/ | `rg sorry SuperHash/Discovery/ SuperHash/DesignLoop/` |
| **V2-M3** | Round-trip validation for RuleCandidates | `scripts/test_roundtrip.py` |
| **V2-M4** | Python scripts pass mypy strict | `mypy --strict scripts/` |
| **V2-M5** | Rule performance budget CI check | `saturateF` on benchmarks within threshold |

## V2-B. Criteria by Node Type

### 1. FUNDACIONAL (N1.0, N1.1, N1.2, N2.1, N2.2, N3.1, N3.2)
<!-- CHECK:V2-F -->

| ID | Theorem | Rationale |
|----|---------|-----------|
| **V2-F1** | `DecidableEq CryptoOp` with block constructors | Backward compatible |
| **V2-F2** | All 4 NodeOps axioms for extended CryptoOp | arity, map, replace, mapReplace |
| **V2-F3** | `processClass_shi_combined` sorry closed | Gates entire v2.0 |
| **V2-F4** | RuleCandidate round-trip TCB validation (D11) | Parser soundness |
| **V2-F5** | `BoundedInput n x → evalBitVec = evalNat` | Abstract-concrete bridge |
| **V2-F6** | BitVec algebraic props (xor assoc/comm) | No Mathlib first principles |

Stress: 0-round blocks, BitVec 0/1/256, empty/identical RuleCandidate LHS/RHS, near-miss counter-examples.
Coherence: every constructor → evalCryptoOp branch + bridge rule + BoundedInput consistency.

### 2. CRITICO (N1.3-N1.5, N2.3, N2.5, N3.3-N3.8, N3.10)
<!-- CHECK:V2-C -->

| ID | Theorem | Rationale |
|----|---------|-----------|
| **V2-C1** | All 4 bridge theorems sound | spnBlock, feistel, sponge, arx |
| **V2-C2** | `rulePool_all_sound` | Dynamic pool invariant |
| **V2-C3** | `extractParetoV2_correct` | Non-linear extraction |
| **V2-C4** | `extractParetoV2_no_dominated` | Pareto property |
| **V2-C5** | `designLoop_preserves_consistency` | Loop invariant |
| **V2-C6** | `designLoop_nonregression` | Quality non-decreasing (D12) |
| **V2-C7** | `designLoop_fuel_decreasing` | Termination |
| **V2-C8** | `pipeline_soundness_v2` 4-part | Master theorem v2.0 |
| **V2-C9** | Non-vacuity for ≥3 Prop hyp theorems | Satisfiability |
| **V2-C10** | v1.0 `pipeline_soundness` unmodified | Regression |

Stress: empty rules → identity, single bridge rule, equally optimal exprs, contradictory rules rejected, 0 fuel → terminate, linear SmoothE → matches v1.0.
Prohibitions: no `Classical.choice` in pipeline, no `simp [*]` in master thm, no proof >50 lines without lemmas.
Coherence: bridges compose with saturateF, SmoothE reduces to linear, loop types chain, v2.0 subsumes v1.0.

### 3. PARALELO — Python (N2.4, N2.6, N2.7, N3.9)
<!-- CHECK:V2-P -->

| ID | Check |
|----|-------|
| **V2-P1** | JSON schema for RuleCandidate |
| **V2-P2** | Round-trip encode/decode = identity |
| **V2-P3** | AXLE pinned to lean-4.28.0 |
| **V2-P4** | LLM deterministic replay |
| **V2-P5** | No sorry/admit generation |
| **V2-P6** | Kill switch + max iterations |

Python = proposal engine. Lean = verification engine. RLVF reward from Lean only.

### 4. HOJA (N1.6, N2.8, N3.11)
<!-- CHECK:V2-H -->

| ID | Check |
|----|-------|
| **V2-H1** | Bridge non-vacuity examples |
| **V2-H2** | E2E demo full v2.0 pipeline |
| **V2-H3** | ≥1 LLM rule compiles + verified |
| **V2-H4** | `#eval` smoke tests all instances |
| **V2-H5** | Master v2.0 non-vacuity |

## V2-C. Formal Properties

| Node | Property | Type | Priority |
|------|----------|------|----------|
| N1.1 | Block arity correct | INVARIANT | P0 |
| N1.3 | Bridge preserves eval | SOUNDNESS | P0 |
| N1.5 | Pipeline backward compat | PRESERVATION | P0 |
| N2.3 | Pool grows only with verified | INVARIANT | P0 |
| N3.2 | Abstract-concrete agreement | EQUIVALENCE | P0 |
| N3.6 | SmoothE → linear reduction | EQUIVALENCE | P1 |
| N3.8 | Loop non-regression | PRESERVATION | P0 |
| N3.10 | Master v2.0 non-vacuity | SOUNDNESS | P0 |

## V2-D. Results (Pending)

## V2-E. Acceptance

v2.0 ready: v1.0 regression + V2-M/F/C/P/H all pass + `pipeline_soundness_v2` proven + E2E non-vacuity + ≥1 LLM rule verified + BitVec bridge proven.

## V2-F. QA Summary

Issues: (1) criteria granularity, (2) no-Mathlib BitVec, (3) formal/informal interface, (4) metaprogramming risk, (5) loop scrutiny. All addressed in criteria above.
