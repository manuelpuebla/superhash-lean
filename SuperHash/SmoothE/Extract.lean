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

/-- foldl dedup doesn't grow beyond input length.
    The accumulator starts empty and adds at most one element per input element. -/
private theorem foldl_dedup_length_le {α : Type} (f : α → α → Bool) :
    ∀ (input : List α) (acc : List α),
    (input.foldl (fun acc pair =>
      if acc.any (fun p => f p pair) then acc else pair :: acc) acc).length
    ≤ acc.length + input.length := by
  intro input
  induction input with
  | nil => intro acc; simp
  | cons x xs ih =>
    intro acc
    simp only [List.foldl, List.length_cons]
    split
    · have := ih acc; omega
    · have h := ih (x :: acc); simp only [List.length_cons] at h; omega

/-- Output length is bounded by suite size.
    Composes: filterMap ≤ input, foldl_dedup ≤ filterMap, filter ≤ dedup. -/
theorem extractParetoV2_length_le (g : EGraph CryptoOp) (suite : CostSuite)
    (costFuel rootId : Nat) :
    (extractParetoV2 g suite costFuel rootId).length ≤ suite.length := by
  simp only [extractParetoV2]
  have h_fm := @List.length_filterMap_le CostFunction _
    (fun cf => extractWithCost g cf costFuel rootId) suite
  have h_dd := foldl_dedup_length_le (fun (p pair : CryptoExpr × SecurityMetrics) => p.2 == pair.2)
    (suite.filterMap fun cf => extractWithCost g cf costFuel rootId) []
  simp at h_dd
  exact Nat.le_trans (List.length_filter_le ..) (Nat.le_trans h_dd h_fm)

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
