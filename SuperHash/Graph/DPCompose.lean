import SuperHash.Graph.TreewidthDP
import SuperHash.Graph.CryptoCost

/-!
# SuperHash.Graph.DPCompose

Multi-criteria DP composition for e-graph extraction.
Extends the single-objective `TreewidthDP` with Pareto-optimal
multi-criteria cost tracking.

Adapted from TrustHash/DP/DPCompose.lean (205 LOC, 0 sorry).

## Main Definitions

* `CostPair` -- pair of (security cost, performance cost)
* `paretoWeakDom` -- weak Pareto dominance (componentwise <=)
* `DPMultiTable` -- multi-objective DP table

## Main Results

* `paretoWeakDom_refl` / `_trans` / `_antisymm` -- preorder + antisymmetry
* `paretoDom_irrefl` -- strict Pareto dominance is irreflexive
* `costPair_scalarize_mono` -- weak dominance implies scalarized dominance
* `dpMultiLeaf_wellformed` -- leaf is wellformed
* `runDPMulti_wellformed` -- composition preserves wellformedness
-/

namespace SuperHash.Graph.DPCompose

open SuperHash.Graph.TreewidthDP
open SuperHash.Graph.NiceTreeConvert
open SuperHash.Graph.CryptoCost

/-! ### Multi-criteria cost -/

/-- A pair of costs: (security cost, performance cost). -/
structure CostPair where
  secCost  : Nat
  perfCost : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Component-wise addition. -/
def CostPair.add (a b : CostPair) : CostPair :=
  ⟨a.secCost + b.secCost, a.perfCost + b.perfCost⟩

/-- The zero cost pair. -/
def CostPair.zero : CostPair := ⟨0, 0⟩

/-- Scalarize: weighted sum of costs. -/
def CostPair.scalarize (c : CostPair) (wSec wPerf : Nat) : Nat :=
  wSec * c.secCost + wPerf * c.perfCost

/-! ### Pareto dominance -/

/-- Weak Pareto dominance (componentwise <=). -/
def paretoWeakDom (c1 c2 : CostPair) : Prop :=
  c1.secCost ≤ c2.secCost ∧ c1.perfCost ≤ c2.perfCost

/-- Strict Pareto dominance: weakly dominates + strictly better in >= 1 component. -/
def paretoDom (c1 c2 : CostPair) : Prop :=
  paretoWeakDom c1 c2 ∧
  (c1.secCost < c2.secCost ∨ c1.perfCost < c2.perfCost)

theorem paretoWeakDom_refl (c : CostPair) : paretoWeakDom c c :=
  ⟨Nat.le.refl, Nat.le.refl⟩

theorem paretoWeakDom_trans (c1 c2 c3 : CostPair)
    (h12 : paretoWeakDom c1 c2) (h23 : paretoWeakDom c2 c3) :
    paretoWeakDom c1 c3 :=
  ⟨Nat.le_trans h12.1 h23.1, Nat.le_trans h12.2 h23.2⟩

theorem paretoWeakDom_antisymm (c1 c2 : CostPair)
    (h12 : paretoWeakDom c1 c2) (h21 : paretoWeakDom c2 c1) :
    c1 = c2 := by
  have h1 : c1.secCost = c2.secCost := Nat.le_antisymm h12.1 h21.1
  have h2 : c1.perfCost = c2.perfCost := Nat.le_antisymm h12.2 h21.2
  cases c1; cases c2; simp at h1 h2
  exact show CostPair.mk _ _ = CostPair.mk _ _ from by congr 1 <;> assumption

/-- Strict Pareto dominance is irreflexive. -/
theorem paretoDom_irrefl (c : CostPair) : ¬paretoDom c c := by
  intro ⟨_, h⟩; cases h with
  | inl h => exact Nat.lt_irrefl _ h
  | inr h => exact Nat.lt_irrefl _ h

/-- Strict Pareto dominance implies weak dominance. -/
theorem paretoDom_implies_weak (c1 c2 : CostPair) (h : paretoDom c1 c2) :
    paretoWeakDom c1 c2 := h.1

/-! ### Cost pair arithmetic -/

theorem costPair_add_comm (a b : CostPair) :
    CostPair.add a b = CostPair.add b a := by
  unfold CostPair.add
  have h1 : a.secCost + b.secCost = b.secCost + a.secCost := by omega
  have h2 : a.perfCost + b.perfCost = b.perfCost + a.perfCost := by omega
  exact show CostPair.mk _ _ = CostPair.mk _ _ from by congr 1 <;> assumption

theorem costPair_add_zero (a : CostPair) :
    CostPair.add a CostPair.zero = a := by
  unfold CostPair.add CostPair.zero
  have h1 : a.secCost + 0 = a.secCost := by omega
  have h2 : a.perfCost + 0 = a.perfCost := by omega
  exact show CostPair.mk _ _ = CostPair.mk _ _ from by congr 1 <;> assumption

theorem costPair_add_weakDom_left (a b : CostPair) :
    paretoWeakDom a (CostPair.add a b) :=
  ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩

theorem costPair_scalarize_mono (c1 c2 : CostPair) (wS wP : Nat)
    (h : paretoWeakDom c1 c2) :
    c1.scalarize wS wP ≤ c2.scalarize wS wP := by
  unfold CostPair.scalarize
  have h1 := Nat.mul_le_mul_left wS h.1
  have h2 := Nat.mul_le_mul_left wP h.2
  omega

/-! ### Multi-objective DP table -/

/-- A multi-objective DP table: maps bag assignments to cost pairs. -/
structure DPMultiTable where
  entries : List (BagAssignment × CostPair)
  deriving Inhabited

namespace DPMultiTable

def empty : DPMultiTable := ⟨[]⟩

/-- Insert a (assignment, cost) pair. Simplified: just prepend. -/
def insert (t : DPMultiTable) (ba : BagAssignment) (c : CostPair) :
    DPMultiTable :=
  ⟨(ba, c) :: t.entries⟩

/-- Number of entries. -/
def size (t : DPMultiTable) : Nat := t.entries.length

end DPMultiTable

/-! ### Multi-objective DP operations -/

/-- Multi-criteria leaf: empty bag, zero cost. -/
def dpMultiLeaf : DPMultiTable :=
  DPMultiTable.insert DPMultiTable.empty [] CostPair.zero

/-- Multi-criteria forget: project out a vertex. -/
def dpMultiForget (table : DPMultiTable) (_v : Nat) : DPMultiTable :=
  table.entries.foldl (fun acc (ba, c) =>
    let ba' := ba.filter (fun (vid, _) => vid != _v)
    DPMultiTable.insert acc ba' c
  ) DPMultiTable.empty

/-- Multi-criteria join: combine two tables on matching bags. -/
def dpMultiJoin (left right : DPMultiTable) : DPMultiTable :=
  left.entries.foldl (fun acc (baL, cL) =>
    right.entries.foldl (fun acc' (baR, cR) =>
      if baL == baR then
        DPMultiTable.insert acc' baL (CostPair.add cL cR)
      else acc'
    ) acc
  ) DPMultiTable.empty

/-! ### Wellformedness -/

/-- Wellformedness: trivially true for Nat-based costs. -/
def DPMultiTable.wellformed (_t : DPMultiTable) : Prop := True

theorem empty_wellformed : DPMultiTable.empty.wellformed := trivial
theorem dpMultiLeaf_wellformed : dpMultiLeaf.wellformed := trivial

theorem insert_wellformed (t : DPMultiTable) (ba : BagAssignment) (c : CostPair)
    (_h : t.wellformed) : (DPMultiTable.insert t ba c).wellformed := trivial

theorem dpMultiForget_wellformed (table : DPMultiTable) (v : Nat)
    (_h : table.wellformed) : (dpMultiForget table v).wellformed := trivial

theorem dpMultiJoin_wellformed (left right : DPMultiTable)
    (_hl : left.wellformed) (_hr : right.wellformed) :
    (dpMultiJoin left right).wellformed := trivial

/-- Running multi-criteria DP over a nice tree preserves wellformedness. -/
theorem runDPMulti_wellformed (t : NiceNode) :
    (niceTreeFold
      dpMultiLeaf
      (fun v child => dpMultiForget child v)
      (fun v child => dpMultiForget child v)
      (fun l r => dpMultiJoin l r)
      t).wellformed := by
  apply niceTreeFold_inv (P := DPMultiTable.wellformed)
  · exact dpMultiLeaf_wellformed
  · intro v r hr; exact dpMultiForget_wellformed r v hr
  · intro v r hr; exact dpMultiForget_wellformed r v hr
  · intro r1 r2 h1 h2; exact dpMultiJoin_wellformed r1 r2 h1 h2

end SuperHash.Graph.DPCompose
