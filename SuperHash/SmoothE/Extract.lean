import SuperHash.SmoothE.CostModel

/-!
# SuperHash.SmoothE.Extract — Non-linear Pareto extraction (N3.5 + N3.6)

v2.0: Extends v1.0's linear scalarization extraction to support
non-linear cost functions via the CostFunction interface.

## SmoothE Concept (D10)
In the full SmoothE paper (ASPLOS 2025), extraction is done via gradient
descent on a differentiable relaxation of the e-graph. Here we provide
a simpler discrete version:
- For each cost function in the suite, extract the best design
- Filter by Pareto dominance
- Return non-dominated front

This captures the key benefit (non-convex Pareto front) without
requiring GPU-accelerated gradient computation.

## Backward Compatibility
Linear cost suite produces identical results to v1.0 extractPareto.
-/

namespace SuperHash

open UnionFind

-- ============================================================
-- extractParetoV2: non-linear cost extraction
-- ============================================================

/-- Extract Pareto-optimal designs using a suite of cost functions.
    For each cost function, extracts the best design, then filters dominated. -/
def extractParetoV2 (g : EGraph CryptoOp) (suite : CostSuite)
    (costFuel rootId : Nat) : List (CryptoExpr × SecurityMetrics) :=
  -- Step 1: Extract one design per cost function
  let candidates := suite.filterMap fun cf =>
    extractWithCost g cf costFuel rootId
  -- Step 2: Dedup by metrics
  let deduped := candidates.foldl (fun acc pair =>
    if acc.any (fun p => p.2 == pair.2) then acc else pair :: acc
  ) []
  -- Step 3: Filter dominated (keep only non-dominated)
  let allMetrics := deduped.map (·.2)
  deduped.filter fun (_, m) => !isDominatedBy m allMetrics

-- ============================================================
-- Correctness properties
-- ============================================================

/-- Output length is bounded by suite size.
    filterMap produces ≤ input, dedup ≤ input, filter ≤ input. -/
theorem extractParetoV2_length_le (g : EGraph CryptoOp) (suite : CostSuite)
    (costFuel rootId : Nat) :
    (extractParetoV2 g suite costFuel rootId).length ≤ suite.length := by
  simp [extractParetoV2]
  sorry -- bound proof: filterMap ≤ input, dedup ≤ input, filter ≤ input

-- ============================================================
-- Backward compatibility with v1.0
-- ============================================================

/-- Extract using v1.0-compatible weight vectors.
    Converts weights to linear cost functions and runs extractParetoV2. -/
def extractParetoCompat (g : EGraph CryptoOp) (weights : List Weights)
    (costFuel rootId : Nat) : List (CryptoExpr × SecurityMetrics) :=
  extractParetoV2 g (weightsToCostSuite weights) costFuel rootId

-- ============================================================
-- Design loop integration
-- ============================================================

/-- Run extraction with standard cost suite (linear + multiplicative). -/
def extractWithStandardCosts (g : EGraph CryptoOp)
    (costFuel rootId : Nat) : List (CryptoExpr × SecurityMetrics) :=
  extractParetoV2 g standardCostSuite costFuel rootId

-- ============================================================
-- Smoke tests
-- ============================================================

open EGraph in
#eval
  let g : EGraph CryptoOp := EGraph.empty
  let (rootId, g) := g.add ⟨CryptoOp.spnBlock 10 0 0⟩
  let result := extractParetoV2 g standardCostSuite 20 rootId
  s!"Standard suite: {result.length} Pareto designs"

end SuperHash
