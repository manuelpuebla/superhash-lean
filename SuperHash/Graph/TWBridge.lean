-- SuperHash/Graph/TWBridge.lean
-- Bridge from computed treewidth to pipeline parameters
-- TreeDecomp -> NiceTreeConvert -> TWBridge -> pipeline treewidth
-- Adapted from TrustHash/TWBridge.lean (117 LOC, 0 sorry)

import SuperHash.Graph.NiceTreeConvert
import SuperHash.Graph.TreeDecomp

namespace SuperHash.Graph.TWBridge

open SuperHash.Graph
open SuperHash.Graph.TreeDecomp
open SuperHash.Graph.NiceTreeConvert
open SuperHash.Graph.EliminationOrder

/-! ## TreewidthAnalysis: computed treewidth with bounds

Bundles the treewidth from tree decomposition with verified bounds. -/

/-- Bundled treewidth analysis for a graph. -/
structure TreewidthAnalysis where
  graphVertices : Nat
  treewidth     : Nat      -- upper bound on treewidth
  niceWidth     : Nat      -- width from nice tree conversion
  numBags       : Nat      -- number of bags in decomposition

/-! ## Computation -/

/-- Compute treewidth analysis from a graph using greedy elimination. -/
def analyzeTreewidth (g : SimpleGraph) : TreewidthAnalysis where
  graphVertices := g.numVertices
  treewidth     := eliminationWidth g
  niceWidth     := (NiceTreeConvert.fromGraph g).width
  numBags       := (TreeDecomp.fromGraph g).size

/-- Compute treewidth for HADES-like cipher.
    Full rounds: constraint graph is K_t (complete), tw = t-1.
    Partial rounds: constraint graph is S_t (star), tw = 1.
    Overall: max of the two sections. -/
def hadesTreewidth (stateWidth : Nat) (hasFullRounds : Bool) : Nat :=
  if hasFullRounds then
    if stateWidth > 1 then stateWidth - 1 else 1
  else 1

/-! ## Bridge theorems -/

/-- HADES treewidth >= 1 when stateWidth >= 1. -/
theorem hadesTreewidth_pos (t : Nat) (_ht : t ≥ 1) (b : Bool) :
    hadesTreewidth t b ≥ 1 := by
  unfold hadesTreewidth
  cases b <;> simp <;> split <;> omega

/-- HADES treewidth with full rounds = t-1 for t >= 2. -/
theorem hadesTreewidth_full (t : Nat) (ht : t ≥ 2) :
    hadesTreewidth t true = t - 1 := by
  unfold hadesTreewidth; simp; omega

/-- HADES treewidth without full rounds = 1. -/
theorem hadesTreewidth_partial (t : Nat) :
    hadesTreewidth t false = 1 := by
  unfold hadesTreewidth; simp

/-- HADES treewidth is monotone in state width with full rounds. -/
theorem hadesTreewidth_mono (t1 t2 : Nat) (h : t1 ≤ t2) :
    hadesTreewidth t1 true ≤ hadesTreewidth t2 true := by
  unfold hadesTreewidth; simp
  split <;> split <;> omega

/-- Elimination width equals tree decomposition width. -/
theorem elimination_eq_decomp (g : SimpleGraph) :
    eliminationWidth g = (TreeDecomp.fromGraph g).width :=
  (fromGraph_width_eq g).symm

/-- K_t has treewidth t-1 (verified computationally). -/
theorem complete_treewidth_3 : eliminationWidth (completeGraph 4) = 3 := by native_decide
theorem complete_treewidth_2 : eliminationWidth (completeGraph 3) = 2 := by native_decide

/-- Star S_t has treewidth 1 (verified computationally). -/
theorem star_treewidth : eliminationWidth (starGraph 4) = 1 := by native_decide

/-- Path P_t has treewidth 1 (verified computationally). -/
theorem path_treewidth : eliminationWidth (pathGraph 4) = 1 := by native_decide

/-! ## Concrete instances -/

/-- Poseidon-3 (t=3): full round treewidth = 2. -/
theorem poseidon3_treewidth : hadesTreewidth 3 true = 2 := by native_decide

/-- Poseidon-9 (t=9): full round treewidth = 8. -/
theorem poseidon9_treewidth : hadesTreewidth 9 true = 8 := by native_decide

/-- Poseidon-3 treewidth >= 1. -/
theorem poseidon3_tw_pos : hadesTreewidth 3 true ≥ 1 := by native_decide

/-- Poseidon-9 treewidth >= 1. -/
theorem poseidon9_tw_pos : hadesTreewidth 9 true ≥ 1 := by native_decide

/-- K4 graph matches HADES treewidth formula. -/
theorem k4_matches_hades : eliminationWidth (completeGraph 4) = hadesTreewidth 4 true := by
  native_decide

/-- K3 graph matches HADES treewidth formula. -/
theorem k3_matches_hades : eliminationWidth (completeGraph 3) = hadesTreewidth 3 true := by
  native_decide

/-! ## Pipeline compatibility

TreewidthAnalysis.treewidth (or hadesTreewidth) can populate pipeline parameters.
The hadesTreewidth function computes max(1, t-1) for full rounds, 1 for partial-only. -/

end SuperHash.Graph.TWBridge
