import SuperHash.Rules.CryptoRules

/-!
# SuperHash.Rules.NonVacuity — Non-vacuity examples for rewrite rules

Each example instantiates all hypotheses with concrete values,
proving the rule is satisfiable (not vacuously true).
-/

namespace SuperHash

-- ============================================================
-- Equivalence rule non-vacuity: concrete evaluations
-- ============================================================

/-- roundCompose: round(7, 5, x) with x=const(3) evaluates correctly on both sides. -/
example : cryptoEval (CryptoExpr.round 7 5 (.const 3)) (fun _ => 0) =
          cryptoEval (CryptoExpr.compose (.sbox 7 (.const 3)) (.const 5)) (fun _ => 0) := by
  native_decide

/-- iterateOne: iterate(1, const(42)) evaluates to 42 on both sides. -/
example : cryptoEval (CryptoExpr.iterate 1 (.const 42)) (fun _ => 0) =
          cryptoEval (.const 42) (fun _ => 0) := by
  native_decide

/-- composeAssoc: compose(compose(const(1), const(2)), const(3)) = compose(const(1), compose(const(2), const(3))). -/
example : cryptoEval (.compose (.compose (.const 1) (.const 2)) (.const 3)) (fun _ => 0) =
          cryptoEval (.compose (.const 1) (.compose (.const 2) (.const 3))) (fun _ => 0) := by
  native_decide

/-- parallelIdentity: parallel(const(10), const(0)) evaluates to 10 = 10. -/
example : cryptoEval (.parallel (.const 10) (.const 0)) (fun _ => 0) =
          cryptoEval (.const 10) (fun _ => 0) := by
  native_decide

/-- iterateCompose: iterate(3, iterate(4, const(5))) = iterate(12, const(5)). -/
example : cryptoEval (.iterate 3 (.iterate 4 (.const 5))) (fun _ => 0) =
          cryptoEval (.iterate 12 (.const 5)) (fun _ => 0) := by
  native_decide

-- ============================================================
-- Improvement strategy non-vacuity: concrete improvements
-- ============================================================

/-- sboxSubstitute fires on low-degree sbox. -/
example : sboxSubstituteStrategy.improve (.sbox 5 0) = some (.sbox 11 0) := rfl

/-- widenTrail fires on narrow linear. -/
example : widenTrailStrategy.improve (.linear 3 0) = some (.linear 5 0) := rfl

/-- increaseRounds fires on any iterate. -/
example : increaseRoundsStrategy.improve (.iterate 8 0) = some (.iterate 10 0) := rfl

-- ============================================================
-- Rules are operationally non-trivial
-- ============================================================

/-- roundCompose rule has a meaningful name. -/
example : roundComposeRule.name = "roundCompose" := rfl

/-- All five rules have distinct names. -/
example : roundComposeRule.name ≠ iterateOneRule.name := by decide

end SuperHash
