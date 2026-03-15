# Insights: SuperHash v2.9.1 — Autopsy Fix (6 findings)

**Fecha**: 2026-03-14
**Base**: v2.9 (60 jobs, 0 sorry)

## Key Findings

### Fix 1 (CRITICAL): Rules use Nat but NodeSemantics uses CryptoSemantics
**Root cause**: The 5 PatternSoundRule instances have `Val := Nat` and prove soundness via `evalCryptoOpSem` (Nat arithmetic). But the E-graph has `NodeSemantics CryptoOp CryptoSemantics` instance that uses `evalCryptoOpCS` (crypto metrics).
**Solution**: Create 5 NEW PatternSoundRule instances with `Val := CryptoSemantics`. The SAME syntactic RewriteRule patterns work — only the soundness proofs change domain. For structural rules (composeAssoc, iterateOne, parallelIdentity), the proofs are analogous because the structure is preserved regardless of domain.
**Key insight from exploration**: PatternSoundRule is polymorphic over Val. The syntactic `RewriteRule` is domain-agnostic. Only `soundness` needs re-proving.

### Fix 2 (CRITICAL): NiceTree introduceCost is identity
**Root cause**: `differentialCostFn.introduceCost = fun _ childCost => childCost` (no-op).
**Real operator** (TrustHash/DP/DPOperations.lean): `childCost + costPerVertex`.
**Solution**: Change to `fun _ childCost => childCost + delta`. Also fix algebraic cost guard.

### Fix 3 (CRITICAL): activeSboxes formula unjustified
**Root cause**: `activeSboxes := branchNumber * (numRounds / 2)` — correct value but no formal link.
**Solution**: Add bridge lemma citing `wide_trail_lower_bound` from LeanHash/MDSMatrix.lean.
**Finding**: The formula IS numerically correct — LeanHash proves `R/2 ≤ branchNumber * (R/2)`.

### Fix 4 (HIGH): Non-vacuity is reflexive (≥ instead of >)
**Root cause**: `g_sat.stats.numNodes ≥ g.stats.numNodes` — always true.
**Solution**: Use roundGraph (which produces 5 nodes from 2) and prove STRICT inequality.

### Fix 5 (HIGH): hrecon — ALREADY CORRECT
**Finding**: `reconstructCrypto` handles ALL 12 CryptoOp constructors with correct child counts matching `CryptoOp.children`. NO CODE CHANGE needed. Add proof theorem.

### Fix 6 (MEDIUM): README says v2.6
**Solution**: Update to v2.9.1 with current metrics.
