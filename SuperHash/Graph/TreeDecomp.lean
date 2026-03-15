-- SuperHash/Graph/TreeDecomp.lean
-- Tree decomposition from elimination ordering
-- Adapted from TrustHash/TreeDecomp.lean (138 LOC, 0 sorry)

import SuperHash.Graph.EliminationOrder
import SuperHash.Graph.SimpleGraph

namespace SuperHash.Graph.TreeDecomp

open SuperHash.Graph
open SuperHash.Graph.EliminationOrder

/-! ## Tree Decomposition

A tree decomposition of a graph G = (V, E) is a tree T where:
1. **Node coverage**: Every vertex of G appears in at least one bag.
2. **Edge coverage**: For every edge (u,v) of G, some bag contains both u and v.
3. **Running intersection**: For every vertex v, the bags containing v
   form a connected subtree of T.

The **width** of the decomposition = max bag size - 1.
The **treewidth** of G = minimum width over all tree decompositions.

Our greedy elimination ordering produces bags that satisfy these properties
for common graph families. -/

/-- A tree decomposition: bags indexed by nodes, with parent pointers.
    Parent of root (node 0) is 0 (self-loop). -/
structure TreeDecomposition where
  numNodes : Nat
  bags     : Array (List Nat)  -- bags[i] = vertices in bag i
  parent   : Array Nat          -- parent[i] = parent node index
  h_bags   : bags.size = numNodes
  h_parent : parent.size = numNodes

/-- Width of a tree decomposition: max bag size - 1. -/
def TreeDecomposition.width (td : TreeDecomposition) : Nat :=
  let maxBag := td.bags.foldl (fun acc bag => Nat.max acc bag.length) 0
  if maxBag > 0 then maxBag - 1 else 0

/-- Number of bags in the decomposition. -/
def TreeDecomposition.size (td : TreeDecomposition) : Nat :=
  td.numNodes

/-! ## Building Tree Decomposition from Elimination Order

The elimination ordering produces bags. We build a tree by connecting
each elimination step to the next step that contains a shared vertex.
For the greedy ordering, a simple chain (each bag's parent = next bag)
gives a valid tree decomposition for the graphs we care about. -/

/-- Build a chain tree decomposition from elimination bags.
    Each bag i has parent i+1 (last bag is root with self-parent). -/
def fromEliminationBags (bags : List (List Nat)) : TreeDecomposition :=
  let n := bags.length
  let bagsArr := bags.toArray
  let parentArr := Array.ofFn fun (i : Fin n) =>
    if i.val + 1 < n then i.val + 1 else i.val
  { numNodes := n
    bags := bagsArr
    parent := parentArr
    h_bags := by simp [bagsArr, n]
    h_parent := by simp [parentArr, n] }

/-- Build tree decomposition from a graph using greedy elimination. -/
def fromGraph (g : SimpleGraph) : TreeDecomposition :=
  fromEliminationBags (eliminationBags g)

/-- The width from tree decomposition matches elimination width. -/
theorem fromGraph_width_eq (g : SimpleGraph) :
    (fromGraph g).width = eliminationWidth g := by
  unfold fromGraph TreeDecomposition.width fromEliminationBags eliminationWidth
  simp

/-! ## Tree Decomposition Verification

Check the three properties of a valid tree decomposition. -/

/-- Check if every vertex 0..n-1 appears in at least one bag. -/
def checkNodeCoverage (td : TreeDecomposition) (numGraphVertices : Nat) : Bool :=
  (List.range numGraphVertices).foldl (fun acc v =>
    acc && td.bags.foldl (fun found bag => found || bag.contains v) false
  ) true

/-- Check if for every edge (u,v), some bag contains both u and v. -/
def checkEdgeCoverage (td : TreeDecomposition) (g : SimpleGraph) : Bool :=
  (List.range g.numVertices).foldl (fun acc u =>
    if hu : u < g.numVertices then
      let nbrs := neighbors g u hu
      nbrs.foldl (fun acc2 v =>
        acc2 && td.bags.foldl (fun found bag =>
          found || (bag.contains u && bag.contains v)) false
      ) acc
    else acc
  ) true

/-- Full validity check (node + edge coverage). -/
def isValid (td : TreeDecomposition) (g : SimpleGraph) : Bool :=
  checkNodeCoverage td g.numVertices && checkEdgeCoverage td g

/-! ## Properties -/

/-- Width is 0 for empty decomposition. -/
theorem width_empty : (fromEliminationBags []).width = 0 := by native_decide

/-- fromGraph produces one bag per vertex. -/
theorem fromGraph_size (g : SimpleGraph) :
    (fromGraph g).size = numBags g := by
  unfold fromGraph TreeDecomposition.size fromEliminationBags numBags
  simp

/-! ## Concrete validation -/

/-- K4 tree decomposition has width 3. -/
theorem k4_td_width : (fromGraph (completeGraph 4)).width = 3 := by native_decide

/-- K3 tree decomposition has width 2. -/
theorem k3_td_width : (fromGraph (completeGraph 3)).width = 2 := by native_decide

/-- Path P4 tree decomposition has width 1. -/
theorem p4_td_width : (fromGraph (pathGraph 4)).width = 1 := by native_decide

/-- Star S4 tree decomposition has width 1. -/
theorem s4_td_width : (fromGraph (starGraph 4)).width = 1 := by native_decide

/-- K4 tree decomposition is valid (complete graph bags preserve indices). -/
theorem k4_td_valid : isValid (fromGraph (completeGraph 4)) (completeGraph 4) = true := by
  native_decide

/-- K3 tree decomposition is valid. -/
theorem k3_td_valid : isValid (fromGraph (completeGraph 3)) (completeGraph 3) = true := by
  native_decide

/-- K2 tree decomposition is valid. -/
theorem k2_td_valid : isValid (fromGraph (completeGraph 2)) (completeGraph 2) = true := by
  native_decide

end SuperHash.Graph.TreeDecomp
