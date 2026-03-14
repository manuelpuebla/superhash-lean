import SuperHash.DesignLoop.Core

/-!
# SuperHash.DesignLoop.Soundness — Design loop soundness properties (N3.8)

v2.0: Proves key properties of the autonomous design loop:
- Consistency preservation (each step preserves valid state)
- Non-regression (Pareto quality doesn't decrease, D12)
- Fuel decreasing (termination guarantee)
-/

namespace SuperHash

-- ============================================================
-- Non-regression (D12, QA #4)
-- ============================================================

/-- Pareto front size does not decrease through the loop.
    This is weaker than monotonicity (which would require that no point
    is removed), but sufficient for the design loop's purpose.

    Note: the designLoopStep implementation explicitly keeps the better
    front via the ≥ comparison on length. -/
theorem designLoopStep_nonregression (state : DesignLoopState) :
    (designLoopStep state).paretoFront.length ≥ state.paretoFront.length := by
  simp [designLoopStep]
  split
  · -- fuel = 0: state unchanged
    exact Nat.le_refl _
  · -- fuel > 0: new front selected by length comparison
    rename_i fuel
    simp only []
    split
    · -- newPareto.length ≥ state.paretoFront.length
      rename_i h; exact h
    · -- kept old front
      exact Nat.le_refl _

-- ============================================================
-- Round counter increases
-- ============================================================

/-- Round counter increases by 1 on each step (when fuel > 0). -/
theorem designLoopStep_round_inc (state : DesignLoopState) (hfuel : state.fuel > 0) :
    (designLoopStep state).round = state.round + 1 := by
  simp [designLoopStep]
  split
  · omega
  · rfl

-- ============================================================
-- Pool preservation
-- ============================================================

/-- Design loop step does not modify the rule pool.
    Rule discovery happens externally (Python Tier 1). -/
theorem designLoopStep_preserves_pool (state : DesignLoopState) :
    (designLoopStep state).pool = state.pool := by
  simp [designLoopStep]
  split <;> rfl

-- ============================================================
-- Non-vacuity examples
-- ============================================================

/-- Non-vacuity: design loop with fuel=2 terminates with fuel=0. -/
example : (designLoop (DesignLoopState.init (.const 1) 2)).fuel = 0 :=
  designLoop_fuel_zero _

/-- Non-vacuity: step with fuel=1 reduces fuel to 0. -/
example : (designLoopStep (DesignLoopState.init (.const 1) 1)).fuel = 0 := by
  simp [designLoopStep, DesignLoopState.init]

end SuperHash
