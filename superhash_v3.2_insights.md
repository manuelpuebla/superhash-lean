# Insights: SuperHash v3.2 — Autopsy Fixes (2 CRITICAL + 3 HIGH + 2 MEDIUM)

**Fecha**: 2026-03-15
**Base**: v3.1.0 (64 jobs, 0 sorry, ~800 thms)

## Infrastructure Analysis for pipeline_soundness_crypto

### Already parametric (works for CryptoSemantics TODAY):
- `NodeSemantics CryptoOp CryptoSemantics` instance (CryptoNodeSemantics.lean)
- `saturateF_preserves_consistent_internal` — polymorphic over Val
- `optimizeF_soundness` / `optimizeF_soundness_complete` — polymorphic
- `ConsistentValuation` — parametric over Val
- `Extractable CryptoOp CryptoExpr` — Val-agnostic
- 3 CS-sound PatternSoundRule instances

### Must be created:
1. `CryptoExpr.evalCS : CryptoExpr → (Nat → CryptoSemantics) → CryptoSemantics`
2. `instance : EvalExpr CryptoExpr CryptoSemantics`
3. `ExtractableSound CryptoOp CryptoExpr CryptoSemantics` — 12-case proof
4. `superhash_pipeline_correct_crypto` — clone of Nat version
5. `pipeline_soundness_crypto` — composed master theorem

### Hardcoded to Nat (need parallel versions):
- `superhash_pipeline_correct` (Integration.lean:56)
- `pipeline_soundness` (MasterTheorem.lean:35)
- `crypto_extractable_sound` (Instances.lean)

## Hypothesis-Echo Audit (12 theorems)

### SecurityNotions.lean — 6 issues:
- `ideal_preimage_bound`: n ≤ n (Nat.le_refl)
- `ideal_second_preimage_bound`: n ≤ n
- `ideal_target_cr_bound`: n ≤ n
- `coll_implies_sec`: returns hypothesis h_sec_ge_coll
- `coll_implies_eSec`: returns hypothesis h_tcr_ge_coll
- `fixed_point_bound`: n ≤ n
- `narrow_pipe_no_margin`: rfl

### ExpanderBounds.lean — 5 issues:
- `lp_security_mono`: returns h_sec, ignores h_calls
- `lp_birthday_lower`: returns h
- `zest_resists_lps_lifting`: returns h_repr_harder
- `lps_collision_cost_linear`: returns h_bound
- `expander_quantum_robustness`: returns h_graph

### UHFConstraint.lean — 1 issue:
- `au_key_length_lower_bound`: returns h_bound

### Fix strategy:
- Remove pure tautologies (n≤n, rfl) — they add LOC without content
- For hypothesis echoes: either prove from structural properties OR convert to `abbrev`/doc comments

## Formula Inconsistency (C10)

**SourceEntropy.lean**: `differentialBits = activeSboxes * (sboxBits - ilog2(delta))`
**SecurityNotions.lean**: `differentialBitsOf = activeMinSboxes * branchNumber`

For AES: 25*(8-2)=150 vs 25*5=125. Different formulas, different results.

**Fix**: SecurityNotions bridge should use sourceEntropy-compatible formula. Need to add `sboxBits` and `logDelta` parameters to the bridge, or compute from CryptoSemantics fields.

## Implementation Plan

### F1: CryptoSemantics Pipeline (CRITICAL)
Create `CryptoExpr.evalCS`, `EvalExpr CryptoExpr CryptoSemantics`, `ExtractableSound`, compose into `pipeline_soundness_crypto`.

### F2: Replace saturation_val_agnostic (CRITICAL)
The real insight: `saturateF` takes `List (RewriteRule Op)` which has NO Val. So `cryptoPatternRulesCS.map (·.rule)` produces the SAME `RewriteRule` list as `cryptoPatternRules.map (·.rule)` IF the .rule fields match. Prove this as a concrete equality or remove the tautology.

### F3: Fix hypothesis echoes (HIGH)
Remove 12 tautological theorems, replace with honest documentation or structural properties.

### F4: Strengthen non-vacuity (HIGH)
Create test with ≥2 rules, ≥3 nodes, actual saturateF application.

### F5: Fix ExpanderBounds naming (HIGH)
Rename mixing_lemma_squared to what it actually proves (associativity helper).

### F6: Fix bridge formula (MEDIUM)
Use sourceEntropy-compatible formula in SecurityNotions bridge.

### F7: Parametric iterateCompose_cs (MEDIUM)
Add instances for n,m ∈ {2,4,8,10,16}.
