import SuperHash.Discovery.RuleCandidate

/-!
# SuperHash.Discovery.RuleVerifier — Rule verification framework

v2.0: Provides the verification pipeline for RuleCandidate instances.
A candidate is verified by constructing a soundness proof attempt:
if `lhsTemplate.eval env = rhsTemplate.eval env` for all `env`,
the rule is sound.

## Verification Strategy
1. Quick check: evaluate on test environments (heuristic pre-filter)
2. Kernel check: attempt to prove `∀ env, lhs.eval env = rhs.eval env`
3. Non-vacuity: construct concrete `example` with specific parameters

For v2.0, kernel verification is done externally via `lake build` on
generated .lean files. This module provides the Lean-side types and
the verified rule construction from candidates.
-/

namespace SuperHash

-- ============================================================
-- Verified rule construction
-- ============================================================

/-- A rule candidate that has been verified by the Lean kernel.
    The `sound` field carries the semantic soundness proof. -/
structure VerifiedRule where
  /-- The original candidate -/
  candidate : RuleCandidate
  /-- Proof that LHS and RHS evaluate identically -/
  sound : ∀ (env : Nat → Nat), candidate.lhsTemplate.eval env = candidate.rhsTemplate.eval env

/-- Construct a VerifiedRule from a RuleCandidate given a soundness proof. -/
def verifyCandidate (rc : RuleCandidate)
    (h : ∀ env : Nat → Nat, rc.lhsTemplate.eval env = rc.rhsTemplate.eval env) :
    VerifiedRule :=
  ⟨rc, h⟩

-- ============================================================
-- Pre-check filter
-- ============================================================

/-- Standard test environments for quick checking.
    Uses 5 environments with different value distributions. -/
def standardTestEnvs : List (Nat → Nat) :=
  [ fun _ => 0      -- all zeros
  , fun _ => 1      -- all ones
  , fun x => x      -- identity
  , fun x => x + 1  -- shifted identity
  , fun _ => 42     -- large constant
  ]

/-- Pre-check a candidate against standard test environments.
    Returns true only if all environments agree. -/
def preCheck (rc : RuleCandidate) : Bool :=
  rc.multiCheck standardTestEnvs

-- ============================================================
-- Concrete verified rule examples
-- ============================================================

/-- SPN block bridge as a VerifiedRule (proof by simp). -/
def verifiedSpnBridge : VerifiedRule :=
  verifyCandidate exampleSpnBridge (by
    intro env
    simp [exampleSpnBridge, CryptoExpr.eval])

/-- Round decomposition as a VerifiedRule (proof by simp). -/
def verifiedRoundDecomp : VerifiedRule :=
  verifyCandidate exampleRoundDecomp (by
    intro env
    simp [exampleRoundDecomp, CryptoExpr.eval])

-- ============================================================
-- Rule performance budget (D13)
-- ============================================================

/-- Performance budget check: a rule is acceptable if evaluating it on a
    test expression completes within a reasonable cost.
    This is a heuristic — the actual CI check runs `saturateF` and measures time. -/
def ruleCostHeuristic (rc : RuleCandidate) : Nat :=
  -- Estimate cost as the maximum depth of LHS and RHS templates
  let rec depth : CryptoExpr → Nat
    | .const _ | .var _ => 1
    | .sbox _ c | .linear _ c | .iterate _ c | .feistelBlock _ c | .spongeBlock _ _ c =>
      1 + depth c
    | .xor l r | .compose l r | .parallel l r | .spnBlock _ l r =>
      1 + max (depth l) (depth r)
    | .round _ _ c => 1 + depth c
    | .arxBlock _ a r x => 1 + max (depth a) (max (depth r) (depth x))
  max (depth rc.lhsTemplate) (depth rc.rhsTemplate)

/-- A rule passes the performance budget if cost ≤ threshold. -/
def RuleCandidate.passesPerformanceBudget (rc : RuleCandidate) (threshold : Nat := 10) : Bool :=
  ruleCostHeuristic rc ≤ threshold

-- Smoke tests
#eval preCheck exampleSpnBridge       -- true
#eval preCheck exampleUnsound          -- false
#eval ruleCostHeuristic exampleSpnBridge    -- 3
#eval ruleCostHeuristic exampleRoundDecomp  -- 3
#eval exampleSpnBridge.passesPerformanceBudget  -- true

end SuperHash
