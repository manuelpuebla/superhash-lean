/-
  SuperHash/Graph/DPOptimal.lean
  Formal specification + proof of DP optimality

  Combines TrustHash/DP/DPOptimalSpec.lean + DPOptimalProof.lean (345 LOC total, 0 sorry).

  Defines the structural validity predicate `ValidNTD` for nice tree
  decompositions and proves: the DP result is both a lower bound AND
  an upper bound, making it tight.

  Reference: VerifiedExtraction/DPOptimality.lean (ValidNTD, DPCompleteInv)
-/

import SuperHash.Graph.CryptoCost

namespace SuperHash.Graph.DPOptimal

open SuperHash.Graph.NiceTreeConvert
open SuperHash.Graph.CryptoCost

/-! ## Valid Nice Tree Decomposition

A `ValidNTD` captures structural invariants that ensure the DP
over the nice tree is well-formed:
1. Leaf: empty base case
2. Introduce: adds a fresh vertex (not already in child's bag)
3. Forget: removes a vertex that IS in the child's bag
4. Join: both children have identical bags -/

/-- Structural validity of a nice tree decomposition. -/
inductive ValidNTD : NiceNode → Prop where
  | leaf : ValidNTD .leaf
  | introduce (v : Nat) (child : NiceNode)
    (hv : v ∉ child.bag)
    (hc : ValidNTD child) :
    ValidNTD (.introduce v child)
  | forget (v : Nat) (child : NiceNode)
    (hv : v ∈ child.bag)
    (hc : ValidNTD child) :
    ValidNTD (.forget v child)
  | join (left right : NiceNode)
    (hbag : left.bag = right.bag)
    (hl : ValidNTD left)
    (hr : ValidNTD right) :
    ValidNTD (.join left right)

/-! ## DP Completeness and Optimality Specifications -/

/-- DP completeness: the DP result at a node equals the tree cost. -/
def DPComplete (costPerVertex : Nat) (tree : NiceNode) : Prop :=
  cryptoDP costPerVertex tree = treeCost costPerVertex tree

/-- DP optimality: the DP result is the MINIMUM over all possible
    cost assignments consistent with the tree structure. -/
def DPOptimal (costPerVertex : Nat) (tree : NiceNode) : Prop :=
  ∀ (f : NiceNode → Nat),
    f .leaf ≥ 1 →
    (∀ v child, f (.introduce v child) ≥ f child + costPerVertex) →
    (∀ v child, f (.forget v child) ≥ f child) →
    (∀ l r, f (.join l r) ≥ f l + f r) →
    cryptoDP costPerVertex tree ≤ f tree

/-- Optimality witness: bundles result, completeness, and optimality. -/
structure DPOptimalityWitness (costPerVertex : Nat) (tree : NiceNode) where
  result    : Nat
  h_result  : result = cryptoDP costPerVertex tree
  h_complete : DPComplete costPerVertex tree
  h_optimal : DPOptimal costPerVertex tree

/-! ## Key Properties of ValidNTD -/

theorem validNTD_leaf : ValidNTD .leaf := ValidNTD.leaf

theorem validNTD_size_pos (t : NiceNode) (hv : ValidNTD t) : 0 < t.size := by
  cases t <;> simp [NiceNode.size] <;> omega

def distinctVertices : NiceNode → List Nat
  | .leaf => []
  | .introduce v child => v :: distinctVertices child
  | .forget _ child => distinctVertices child
  | .join left right => distinctVertices left ++ distinctVertices right

theorem validNTD_intro_fresh (v : Nat) (child : NiceNode)
    (h : ValidNTD (.introduce v child)) : v ∉ child.bag := by
  cases h with | introduce _ _ hv _ => exact hv

theorem validNTD_forget_present (v : Nat) (child : NiceNode)
    (h : ValidNTD (.forget v child)) : v ∈ child.bag := by
  cases h with | forget _ _ hv _ => exact hv

theorem validNTD_join_bags (l r : NiceNode)
    (h : ValidNTD (.join l r)) : l.bag = r.bag := by
  cases h with | join _ _ hbag _ _ => exact hbag

/-! ## DPComplete always holds (definitional equality) -/

theorem dpComplete_always (c : Nat) (t : NiceNode) : DPComplete c t :=
  cryptoDP_eq_treeCost c t

/-! ## Core Optimality Proof

By induction on ValidNTD, using structural constraints on f
and the definition of cryptoDP via niceTreeFold. -/

/-- **Main theorem**: For any valid nice tree decomposition, the crypto DP
    computes the optimal (minimum) cost over all cost functions that
    respect the tree structure. -/
theorem dp_optimal_of_validNTD (c : Nat) (tree : NiceNode)
    (hvalid : ValidNTD tree)
    (f : NiceNode → Nat)
    (hf_leaf : f .leaf ≥ 1)
    (hf_intro : ∀ v child, f (.introduce v child) ≥ f child + c)
    (hf_forget : ∀ v child, f (.forget v child) ≥ f child)
    (hf_join : ∀ l r, f (.join l r) ≥ f l + f r) :
    cryptoDP c tree ≤ f tree := by
  induction hvalid with
  | leaf =>
    show dpLeaf ≤ f .leaf
    simp [dpLeaf]; exact hf_leaf
  | introduce v child _ _ ih =>
    show dpIntroduce c v (cryptoDP c child) ≤ f (.introduce v child)
    simp [dpIntroduce]
    have h2 := hf_intro v child
    omega
  | forget v child _ _ ih =>
    show dpForget v (cryptoDP c child) ≤ f (.forget v child)
    simp [dpForget]
    have h2 := hf_forget v child
    omega
  | join left right _ _ _ ihl ihr =>
    show dpJoin (cryptoDP c left) (cryptoDP c right) ≤ f (.join left right)
    simp [dpJoin]
    have h3 := hf_join left right
    omega

/-- ValidNTD implies DPOptimal. -/
theorem dpOptimal_of_validNTD (c : Nat) (tree : NiceNode)
    (hvalid : ValidNTD tree) : DPOptimal c tree := by
  intro f hf_leaf hf_intro hf_forget hf_join
  exact dp_optimal_of_validNTD c tree hvalid f hf_leaf hf_intro hf_forget hf_join

/-! ## Full Optimality Witness Construction -/

def mkOptimalityWitness (c : Nat) (tree : NiceNode) (hvalid : ValidNTD tree) :
    DPOptimalityWitness c tree where
  result := cryptoDP c tree
  h_result := rfl
  h_complete := dpComplete_always c tree
  h_optimal := dpOptimal_of_validNTD c tree hvalid

/-! ## Corollaries -/

/-- The DP result is tight: it equals treeCost AND is minimal. -/
theorem dp_tight_of_validNTD (c : Nat) (tree : NiceNode)
    (hvalid : ValidNTD tree) :
    cryptoDP c tree = treeCost c tree
    ∧ DPOptimal c tree :=
  ⟨cryptoDP_eq_treeCost c tree, dpOptimal_of_validNTD c tree hvalid⟩

/-- SecurityDP is optimal: min of two optimal DPs is optimal. -/
theorem securityDP_optimal_of_validNTD (delta degree : Nat) (tree : NiceNode)
    (hvalid : ValidNTD tree) :
    ∀ (f g : NiceNode → Nat),
      f .leaf ≥ 1 → g .leaf ≥ 1 →
      (∀ v child, f (.introduce v child) ≥ f child + delta) →
      (∀ v child, g (.introduce v child) ≥ g child + degree) →
      (∀ v child, f (.forget v child) ≥ f child) →
      (∀ v child, g (.forget v child) ≥ g child) →
      (∀ l r, f (.join l r) ≥ f l + f r) →
      (∀ l r, g (.join l r) ≥ g l + g r) →
      securityDP delta degree tree ≤ min (f tree) (g tree) := by
  intro f g hfl hgl hfi hgi hff hgf hfj hgj
  have h1 := dp_optimal_of_validNTD delta tree hvalid f hfl hfi hff hfj
  have h2 := dp_optimal_of_validNTD degree tree hvalid g hgl hgi hgf hgj
  simp only [securityDP, differentialDP, algebraicDP]
  omega

/-! ## Closed-form: DP via countIntroduce -/

def leafCount : NiceNode → Nat
  | .leaf => 1
  | .introduce _ child => leafCount child
  | .forget _ child => leafCount child
  | .join left right => leafCount left + leafCount right

def introCount : NiceNode → Nat
  | .leaf => 0
  | .introduce _ child => 1 + introCount child
  | .forget _ child => introCount child
  | .join left right => introCount left + introCount right

/-- cryptoDP equals leafCount + introCount * c. -/
theorem dp_eq_formula (c : Nat) (tree : NiceNode) :
    cryptoDP c tree = leafCount tree + introCount tree * c := by
  induction tree with
  | leaf =>
    show 1 = 1 + 0 * c
    omega
  | introduce v child ih =>
    show cryptoDP c child + c = leafCount child + (1 + introCount child) * c
    rw [Nat.add_mul]; simp [Nat.one_mul]; omega
  | forget v child ih =>
    show cryptoDP c child = leafCount child + introCount child * c
    exact ih
  | join left right ihl ihr =>
    show cryptoDP c left + cryptoDP c right
      = (leafCount left + leafCount right) + (introCount left + introCount right) * c
    rw [Nat.add_mul]; omega

theorem leafCount_pos (tree : NiceNode) : leafCount tree ≥ 1 := by
  induction tree with
  | leaf => simp [leafCount]
  | introduce _ child ih => simp only [leafCount]; exact ih
  | forget _ child ih => simp only [leafCount]; exact ih
  | join left _ ihl _ => simp only [leafCount]; omega

theorem dp_ge_leafCount (c : Nat) (tree : NiceNode) :
    cryptoDP c tree ≥ leafCount tree := by
  have := dp_eq_formula c tree; omega

/-! ## Concrete Validation -/

private def validTree1 : NiceNode := .introduce 0 (.introduce 1 .leaf)
private def validTree2 : NiceNode := .join (.introduce 0 .leaf) (.introduce 0 .leaf)
private def validTree3 : NiceNode :=
  .forget 0 (.introduce 0 (.introduce 1 .leaf))

theorem validTree1_valid : ValidNTD validTree1 :=
  ValidNTD.introduce 0 _ (by simp [NiceNode.bag]) <|
  ValidNTD.introduce 1 _ (by simp [NiceNode.bag]) <|
  ValidNTD.leaf

theorem validTree2_valid : ValidNTD validTree2 :=
  ValidNTD.join _ _ rfl
    (ValidNTD.introduce 0 _ (by simp [NiceNode.bag]) ValidNTD.leaf)
    (ValidNTD.introduce 0 _ (by simp [NiceNode.bag]) ValidNTD.leaf)

theorem validTree3_valid : ValidNTD validTree3 :=
  ValidNTD.forget 0 _
    (by simp [NiceNode.bag])
    (ValidNTD.introduce 0 _ (by simp [NiceNode.bag])
      (ValidNTD.introduce 1 _ (by simp [NiceNode.bag]) ValidNTD.leaf))

theorem opt_tree1_witness :
    (mkOptimalityWitness 4 validTree1 validTree1_valid).result = 9 := by
  native_decide

theorem opt_tree2_witness :
    (mkOptimalityWitness 3 validTree2 validTree2_valid).result = 8 := by
  native_decide

theorem dp_formula_chain : cryptoDP 4 validTree1 = 9 := by native_decide
theorem dp_formula_join : cryptoDP 3 validTree2 = 8 := by native_decide

end SuperHash.Graph.DPOptimal
