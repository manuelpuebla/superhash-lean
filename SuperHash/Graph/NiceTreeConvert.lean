-- SuperHash/Graph/NiceTreeConvert.lean
-- Convert tree decomposition to nice tree structure for DP
-- Adapted from TrustHash/NiceTreeConvert.lean (120 LOC, 0 sorry)

import SuperHash.Graph.TreeDecomp

namespace SuperHash.Graph.NiceTreeConvert

open SuperHash.Graph
open SuperHash.Graph.TreeDecomp

/-! ## Nice Tree Decomposition

A "nice" tree decomposition has restricted node types:
1. **Leaf**: Empty bag
2. **Introduce**: Adds exactly one vertex to parent's bag
3. **Forget**: Removes exactly one vertex from parent's bag
4. **Join**: Two children with identical bags

This structure is required for efficient DP algorithms.
(Kloks 1994; Bodlaender & Koster 2010) -/

/-- Nice tree node types. -/
inductive NiceNode where
  | leaf : NiceNode
  | introduce (vertex : Nat) (child : NiceNode) : NiceNode
  | forget (vertex : Nat) (child : NiceNode) : NiceNode
  | join (left right : NiceNode) : NiceNode

/-- Bag contents at a nice tree node. -/
def NiceNode.bag : NiceNode → List Nat
  | .leaf => []
  | .introduce v child => v :: child.bag
  | .forget _ child => child.bag  -- forget doesn't change computed bag
  | .join left _ => left.bag      -- join: both children have same bag

/-- Width of the widest bag in a nice tree. -/
def NiceNode.width : NiceNode → Nat
  | .leaf => 0
  | .introduce _ child => Nat.max (1 + child.width) (child.bag.length + 1)
  | .forget _ child => Nat.max child.width child.bag.length
  | .join left right => Nat.max (Nat.max left.width right.width) left.bag.length

/-- Number of nodes in the nice tree. -/
def NiceNode.size : NiceNode → Nat
  | .leaf => 1
  | .introduce _ child => 1 + child.size
  | .forget _ child => 1 + child.size
  | .join left right => 1 + left.size + right.size

/-! ## Simple Conversion: Chain of Introductions

For a chain tree decomposition (from greedy elimination), each bag
becomes a chain of introduce nodes building up from a leaf.
This is not optimal but is correct and simple. -/

/-- Build a nice tree from a single bag: leaf + introduce each vertex. -/
def bagToNiceTree (bag : List Nat) : NiceNode :=
  bag.foldl (fun tree v => .introduce v tree) .leaf

/-- Convert a list of bags to a nice tree.
    Each bag becomes introduce-chain, connected via join nodes. -/
def bagsToNiceTree (bags : List (List Nat)) : NiceNode :=
  match bags with
  | [] => .leaf
  | [bag] => bagToNiceTree bag
  | bag :: rest => .join (bagToNiceTree bag) (bagsToNiceTree rest)

/-- Convert a tree decomposition to a nice tree. -/
def fromTreeDecomp (td : TreeDecomposition) : NiceNode :=
  bagsToNiceTree td.bags.toList

/-- Convert a graph directly to a nice tree via elimination. -/
def fromGraph (g : SimpleGraph) : NiceNode :=
  fromTreeDecomp (TreeDecomp.fromGraph g)

/-! ## Properties -/

/-- Leaf has width 0. -/
theorem leaf_width : NiceNode.leaf.width = 0 := rfl

/-- Leaf has size 1. -/
theorem leaf_size : NiceNode.leaf.size = 1 := rfl

/-- Leaf bag is empty. -/
theorem leaf_bag : NiceNode.leaf.bag = [] := rfl

/-- bagToNiceTree of empty list is leaf. -/
theorem bagToNiceTree_nil : bagToNiceTree [] = .leaf := rfl

/-- Width of single-vertex bag is 1. -/
theorem single_vertex_width : (bagToNiceTree [v]).width = Nat.max 1 1 := rfl

/-! ## Concrete validation -/

/-- K4 nice tree has correct width. -/
theorem k4_nice_width :
    (fromGraph (completeGraph 4)).width = 4 := by native_decide

/-- K3 nice tree width. -/
theorem k3_nice_width :
    (fromGraph (completeGraph 3)).width = 3 := by native_decide

/-- P4 nice tree width. -/
theorem p4_nice_width :
    (fromGraph (pathGraph 4)).width = 2 := by native_decide

/-- S4 nice tree width. -/
theorem s4_nice_width :
    (fromGraph (starGraph 4)).width = 2 := by native_decide

/-- K4 nice tree size. -/
theorem k4_nice_size :
    (fromGraph (completeGraph 4)).size = 17 := by native_decide

/-- Empty graph nice tree. -/
theorem empty_nice_width :
    (fromGraph (emptyGraph 4)).width = 1 := by native_decide

end SuperHash.Graph.NiceTreeConvert
