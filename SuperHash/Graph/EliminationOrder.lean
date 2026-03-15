-- SuperHash/Graph/EliminationOrder.lean
-- Greedy min-degree elimination ordering for treewidth upper bound
-- Adapted from TrustHash/EliminationOrder.lean (92 LOC, 0 sorry)

import SuperHash.Graph.SimpleGraph

namespace SuperHash.Graph.EliminationOrder

open SuperHash.Graph

/-! ## Greedy Min-Degree Elimination

The greedy elimination algorithm gives an upper bound on treewidth:
1. While graph has vertices:
   a. Pick vertex v with minimum degree
   b. Record bag = {v} U neighbors(v)
   c. Make neighbors of v a clique (fill-in)
   d. Remove v from the graph
2. Treewidth <= max(|bag|) - 1

This is a heuristic -- it gives the EXACT treewidth for complete graphs,
paths, stars, and many structured graphs. For general graphs it's an
upper bound. (Bodlaender & Koster 2010) -/

/-- One step of greedy elimination: remove min-degree vertex, fill in neighbors.
    Returns (reduced graph, bag for this step). -/
def eliminationStep (g : SimpleGraph) : SimpleGraph × List Nat :=
  if g.numVertices == 0 then (g, [])
  else
    let v := minDegreeVertex g
    if hv : v < g.numVertices then
      let nbrs := neighbors g v hv
      let bag := v :: nbrs
      let g' := makeClique g nbrs
      let g'' := removeVertex g' v
      (g'', bag)
    else (g, [])  -- defensive: shouldn't happen

/-- Compute all elimination bags via greedy min-degree ordering.
    Uses fuel = initial numVertices for termination. -/
def eliminationBags (g : SimpleGraph) : List (List Nat) :=
  go g g.numVertices []
where
  go (g : SimpleGraph) (fuel : Nat) (acc : List (List Nat)) : List (List Nat) :=
    match fuel with
    | 0 => acc.reverse
    | n + 1 =>
      if g.numVertices == 0 then acc.reverse
      else
        let (g', bag) := eliminationStep g
        go g' n (bag :: acc)

/-- Treewidth upper bound from greedy elimination: max bag size - 1. -/
def eliminationWidth (g : SimpleGraph) : Nat :=
  let bags := eliminationBags g
  let maxBagSize := bags.foldl (fun acc bag => Nat.max acc bag.length) 0
  if maxBagSize > 0 then maxBagSize - 1 else 0

/-- Number of bags produced by elimination (= original number of vertices). -/
def numBags (g : SimpleGraph) : Nat :=
  (eliminationBags g).length

/-! ## Concrete validation

These tests verify that our greedy algorithm produces correct treewidth
upper bounds for graphs with known exact treewidth. -/

/-- Complete graph K_4 has treewidth 3. -/
theorem complete4_width : eliminationWidth (completeGraph 4) = 3 := by native_decide

/-- Complete graph K_3 has treewidth 2. -/
theorem complete3_width : eliminationWidth (completeGraph 3) = 2 := by native_decide

/-- Path graph P_4 has treewidth 1. -/
theorem path4_width : eliminationWidth (pathGraph 4) = 1 := by native_decide

/-- Star graph S_4 has treewidth 1. -/
theorem star4_width : eliminationWidth (starGraph 4) = 1 := by native_decide

/-- Empty graph has treewidth 0. -/
theorem empty4_width : eliminationWidth (emptyGraph 4) = 0 := by native_decide

/-- Single vertex has treewidth 0. -/
theorem single_width : eliminationWidth (completeGraph 1) = 0 := by native_decide

/-- K_2 has treewidth 1. -/
theorem complete2_width : eliminationWidth (completeGraph 2) = 1 := by native_decide

/-- Elimination produces one bag per vertex. -/
theorem complete4_bags : numBags (completeGraph 4) = 4 := by native_decide

end SuperHash.Graph.EliminationOrder
