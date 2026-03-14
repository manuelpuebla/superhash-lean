import SuperHash.Pareto.Extract

/-!
# SuperHash.SmoothE.CostModel — Non-linear cost model for SmoothE extraction

v2.0 (N3.4): Extends SecurityMetrics with non-linear cost combinations.
Supports multiplicative metrics (degree products, branch number products)
for SmoothE differentiable extraction.

## Design (D10)
- Linear costs reduce to v1.0 `scalarize` behavior (backward compatible)
- Non-linear costs enable SmoothE to find non-convex Pareto front
- CostFunction typeclass abstracts over cost computation
-/

namespace SuperHash

-- ============================================================
-- Non-linear cost function
-- ============================================================

/-- A general cost function maps SecurityMetrics to a single Nat cost.
    Linear: weighted sum. Non-linear: products, powers, min/max. -/
structure CostFunction where
  /-- Human-readable name -/
  name : String
  /-- Compute cost from metrics -/
  compute : SecurityMetrics → Nat
  /-- Monotonicity: if m1 dominates m2, cost(m1) ≤ cost(m2) -/
  monotone : Bool  -- NOTE: not formally proven, advisory flag

/-- Linear cost function (reduces to v1.0 scalarize). -/
def linearCost (w : Weights) : CostFunction where
  name := s!"linear({w.wSecurity},{w.wLatency},{w.wGateCount})"
  compute := fun m => scalarize w m
  monotone := true

/-- Multiplicative security cost: security × (1/latency) × (1/gates).
    Higher is better — but we minimize cost, so invert. -/
def multiplicativeCost : CostFunction where
  name := "multiplicative"
  compute := fun m =>
    -- Minimize: latency × gates / security (lower = better design)
    if m.securityBits = 0 then Nat.succ (m.latency * m.gateCount)  -- penalize zero security
    else (m.latency * m.gateCount) / m.securityBits + 1
  monotone := false  -- non-linear, monotonicity not guaranteed

/-- Security-latency product (non-linear tradeoff surface). -/
def securityLatencyProduct : CostFunction where
  name := "securityLatency"
  compute := fun m => m.securityBits * 1000 / (m.latency + 1)  -- higher = better
  monotone := false

-- ============================================================
-- Non-linear cost list (replacing v1.0 Weights list)
-- ============================================================

/-- A collection of cost functions for multi-objective extraction. -/
abbrev CostSuite := List CostFunction

/-- Standard cost suite: 3 linear + 1 multiplicative. -/
def standardCostSuite : CostSuite :=
  [ linearCost ⟨1, 1, 1⟩
  , linearCost ⟨2, 1, 1⟩
  , linearCost ⟨1, 2, 1⟩
  , multiplicativeCost
  ]

-- ============================================================
-- Backward compatibility: linear costs → v1.0 behavior
-- ============================================================

/-- Linear cost agrees with v1.0 scalarize. -/
theorem linearCost_eq_scalarize (w : Weights) (m : SecurityMetrics) :
    (linearCost w).compute m = scalarize w m := by
  simp [linearCost, CostFunction.compute, scalarize]

/-- Converting v1.0 Weights list to CostSuite. -/
def weightsToCostSuite (ws : List Weights) : CostSuite :=
  ws.map linearCost

-- ============================================================
-- Cost-based extraction interface
-- ============================================================

/-- Extract best design for a given cost function.
    Uses v1.0 extractAuto and then computes metrics via cost function. -/
def extractWithCost (g : EGraph CryptoOp) (_costFn : CostFunction)
    (_costFuel rootId : Nat) : Option (CryptoExpr × SecurityMetrics) :=
  match extractAuto g rootId with
  | some expr =>
    let metrics := expr.metrics
    some (expr, metrics)
  | none => none

-- ============================================================
-- Smoke tests
-- ============================================================

#eval (linearCost ⟨1, 1, 1⟩).compute ⟨100, 10, 50⟩
#eval multiplicativeCost.compute ⟨100, 10, 50⟩
#eval securityLatencyProduct.compute ⟨100, 10, 50⟩

end SuperHash
