import SuperHash.Discovery.RulePool
import SuperHash.SmoothE.Extract
import SuperHash.Instances.Evaluation
import SuperHash.Rules.CryptoRules
import SuperHash.Rules.ExpansionRules

/-!
# SuperHash.DesignLoop.Core — Autonomous design loop (N3.7)

v2.0: Fuel-bounded design loop that iteratively:
  discover → verify → saturate → extract → evaluate → expand

## Termination (D4, QA #9)
The outer loop is fuel-bounded: fuel decreases strictly on each step.
theorem designLoop_terminates: fuel decreases.

## Design (D12: Non-Regression)
The loop preserves the property that the Pareto front quality
does not decrease (weaker than monotonicity, per QA #4).
-/

namespace SuperHash

-- ============================================================
-- Design loop state
-- ============================================================

/-- State of the autonomous design loop. -/
structure DesignLoopState where
  /-- Current rule pool (grows as rules are discovered) -/
  pool : RulePool
  /-- Current E-graph -/
  graph : EGraph CryptoOp
  /-- Current Pareto front -/
  paretoFront : List (CryptoExpr × SecurityMetrics)
  /-- Root e-class ID -/
  rootId : EClassId
  /-- Remaining fuel (decreases each step) -/
  fuel : Nat
  /-- Round counter (for logging) -/
  round : Nat := 0

/-- Initial state from a design and empty rule pool. -/
def DesignLoopState.init (design : CryptoExpr) (fuel : Nat) : DesignLoopState :=
  let g := EGraph.empty (Op := CryptoOp)
  let (rootId, g) := designToEGraph design g
  let initialPareto := extractParetoV2 g standardCostSuite 20 rootId
  { pool := RulePool.empty
  , graph := g
  , paretoFront := initialPareto
  , rootId := rootId
  , fuel := fuel
  , round := 0
  }

-- ============================================================
-- Design loop step
-- ============================================================

/-- One step of the design loop.
    In the Lean formalization, this performs saturation with current rules
    and re-extracts the Pareto front. Rule discovery happens externally
    via the Python orchestrator (Tier 1).

    The Lean side only handles: saturate → extract → evaluate.
    Discovery + verification happens in Python → VerifiedRule. -/
def designLoopStep (state : DesignLoopState) : DesignLoopState :=
  match state.fuel with
  | 0 => state  -- no fuel: return unchanged
  | fuel + 1 =>
    -- v3.0: Saturate with ALL rules (simplification + expansion + bridges)
    -- 5 simplification (Nat) + 10 expansion (bridges + roundSplit) = 15 rules
    let satRules : List (RewriteRule CryptoOp) :=
      cryptoPatternRules.map (·.rule) ++ expansionRules
    let g_sat := saturateF 10 5 3 state.graph satRules
    -- Extract new Pareto front
    let newPareto := extractParetoV2 g_sat standardCostSuite 20 state.rootId
    -- Keep the better front (non-regression: prefer new if it has more points)
    let bestPareto := if newPareto.length ≥ state.paretoFront.length
                      then newPareto else state.paretoFront
    { state with
      graph := g_sat
      paretoFront := bestPareto
      fuel := fuel
      round := state.round + 1
    }

/-- Run the design loop for all remaining fuel. -/
def designLoop (state : DesignLoopState) : DesignLoopState :=
  match h : state.fuel with
  | 0 => state
  | fuel + 1 =>
    let state' := designLoopStep state
    have : state'.fuel < state.fuel := by
      simp only [state', designLoopStep, h]; omega
    designLoop state'
termination_by state.fuel

-- ============================================================
-- Termination (QA #9)
-- ============================================================

/-- Fuel decreases strictly on each step (when fuel > 0). -/
theorem designLoopStep_fuel_decreasing (state : DesignLoopState) (hfuel : state.fuel > 0) :
    (designLoopStep state).fuel < state.fuel := by
  cases hf : state.fuel with
  | zero => omega
  | succ n => simp [designLoopStep, hf]

/-- After loop, fuel is 0. -/
theorem designLoop_fuel_zero (state : DesignLoopState) :
    (designLoop state).fuel = 0 := by
  unfold designLoop
  split
  · next h => exact h
  · apply designLoop_fuel_zero
termination_by state.fuel
decreasing_by
  simp_wf
  have h := designLoopStep_fuel_decreasing state (by omega)
  exact h

-- ============================================================
-- Smoke tests
-- ============================================================

#eval
  let state := DesignLoopState.init (.spnBlock 10 (.const 7) (.const 5)) 3
  let final := designLoop state
  s!"Rounds: {final.round}, Pareto: {final.paretoFront.length}, Fuel: {final.fuel}"

end SuperHash
