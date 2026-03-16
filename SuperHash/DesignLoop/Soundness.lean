import SuperHash.DesignLoop.Core

/-!
# SuperHash.DesignLoop.Soundness — Design loop soundness properties (N3.8)

v2.0/v4.5.1: Proves key properties of the autonomous design loop:
- Consistency preservation (each step preserves valid state)
- Non-regression in SIZE (Pareto front length doesn't decrease, D12)
- Non-regression in QUALITY (bestSecurityBits doesn't decrease, v4.5.1 N6)
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
  · -- fuel > 0: new front selected by length ∧ quality comparison
    rename_i fuel
    simp only []
    split
    · -- length ≥ AND quality ≥
      rename_i h; exact h.1
    · -- kept old front
      exact Nat.le_refl _

-- ============================================================
-- Quality non-regression (v4.5.1 — N6)
-- ============================================================

/-- Best security bits does not decrease through the loop step.
    v4.5.1: quality-aware non-regression — bestSecurityBits is non-decreasing.
    Proof: the ∧ condition in designLoopStep ensures both length AND quality
    must improve for the new front to be selected. -/
theorem designLoopStep_best_nondecreasing (state : DesignLoopState) :
    bestSecurityBits (designLoopStep state).paretoFront ≥
    bestSecurityBits state.paretoFront := by
  simp [designLoopStep]
  split
  · exact Nat.le_refl _
  · rename_i fuel
    simp only []
    split
    · rename_i h; exact h.2
    · exact Nat.le_refl _

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

/-- Design loop preserves the rule pool through all iterations.
    Composed inductively from designLoopStep_preserves_pool. -/
theorem designLoop_pool_eq (state : DesignLoopState) :
    (designLoop state).pool = state.pool := by
  unfold designLoop
  split
  · rfl
  · have h_step := designLoopStep_preserves_pool state
    have h_ih := designLoop_pool_eq (designLoopStep state)
    rw [h_ih, h_step]
termination_by state.fuel
decreasing_by
  simp_wf
  exact designLoopStep_fuel_decreasing state (by omega)

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
