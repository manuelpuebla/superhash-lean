/-
  SuperHash/Graph/CryptoCost.lean
  Crypto-specific cost functions for DP + NiceTree catamorphism + DPOperations + SecurityDP

  Consolidates TrustHash DP/NiceTree.lean + DP/CryptoCost.lean + DP/DPOperations.lean
  + DP/SecurityDP.lean into a single file with zero external dependencies.

  Reference: DynamicTreeProg/CostFunction.lean (additiveCost, additiveCost_append)
  Reference: DynamicTreeProg/NiceTree.lean (treeFold, treeFold_inv, treeFold_lower_bound)
  Adapted from TrustHash/DP/{NiceTree,CryptoCost,DPOperations,SecurityDP}.lean (0 sorry each)
-/

import SuperHash.Graph.NiceTreeConvert

namespace SuperHash.Graph.CryptoCost

open SuperHash.Graph.NiceTreeConvert

-- ============================================================
-- Part 1: NiceTree catamorphism (from TrustHash/DP/NiceTree.lean)
-- ============================================================

/-! ## Bottom-up fold (catamorphism) on nice trees -/

/-- Bottom-up fold on a nice tree decomposition.
    Four operations, one per node type:
    - `fLeaf`: base case (empty bag)
    - `fIntro v r`: introduce vertex `v`, child result `r`
    - `fForget v r`: forget vertex `v`, child result `r`
    - `fJoin r1 r2`: join two subtree results -/
def niceTreeFold {β : Type} (fLeaf : β) (fIntro : Nat → β → β)
    (fForget : Nat → β → β) (fJoin : β → β → β) : NiceNode → β
  | .leaf => fLeaf
  | .introduce v child => fIntro v (niceTreeFold fLeaf fIntro fForget fJoin child)
  | .forget v child => fForget v (niceTreeFold fLeaf fIntro fForget fJoin child)
  | .join left right =>
    fJoin (niceTreeFold fLeaf fIntro fForget fJoin left)
          (niceTreeFold fLeaf fIntro fForget fJoin right)

/-! ## Invariant preservation -/

/-- If all four operations preserve predicate `P`,
    then `niceTreeFold` preserves `P`. -/
theorem niceTreeFold_inv {β : Type} (P : β → Prop)
    (fLeaf : β) (fIntro : Nat → β → β) (fForget : Nat → β → β) (fJoin : β → β → β)
    (h_leaf : P fLeaf)
    (h_intro : ∀ v r, P r → P (fIntro v r))
    (h_forget : ∀ v r, P r → P (fForget v r))
    (h_join : ∀ r1 r2, P r1 → P r2 → P (fJoin r1 r2))
    (t : NiceNode) :
    P (niceTreeFold fLeaf fIntro fForget fJoin t) := by
  induction t with
  | leaf => exact h_leaf
  | introduce v child ih => exact h_intro v _ ih
  | forget v child ih => exact h_forget v _ ih
  | join left right ihl ihr => exact h_join _ _ ihl ihr

/-- Invariant + extension relation through niceTreeFold. -/
theorem niceTreeFold_inv_ext {β : Type}
    (P : β → Prop) (Ext : β → β → Prop)
    (fLeaf : β) (fIntro : Nat → β → β) (fForget : Nat → β → β) (fJoin : β → β → β)
    (h_leaf : P fLeaf)
    (h_intro : ∀ v r, P r → P (fIntro v r) ∧ Ext r (fIntro v r))
    (h_forget : ∀ v r, P r → P (fForget v r) ∧ Ext r (fForget v r))
    (h_join : ∀ r1 r2, P r1 → P r2 →
      P (fJoin r1 r2) ∧ Ext r1 (fJoin r1 r2) ∧ Ext r2 (fJoin r1 r2))
    (t : NiceNode) :
    P (niceTreeFold fLeaf fIntro fForget fJoin t) := by
  induction t with
  | leaf => exact h_leaf
  | introduce v child ih => exact (h_intro v _ ih).1
  | forget v child ih => exact (h_forget v _ ih).1
  | join left right ihl ihr => exact (h_join _ _ ihl ihr).1

/-- Pair state invariant: if operations preserve `Inv` on second component,
    then niceTreeFold on pairs preserves `Inv`. -/
theorem niceTreeFold_pair_inv {β S : Type}
    (Inv : S → Prop)
    (fLeaf : β × S) (fIntro : Nat → β × S → β × S)
    (fForget : Nat → β × S → β × S) (fJoin : β × S → β × S → β × S)
    (h_leaf : Inv fLeaf.2)
    (h_intro : ∀ v p, Inv p.2 → Inv (fIntro v p).2)
    (h_forget : ∀ v p, Inv p.2 → Inv (fForget v p).2)
    (h_join : ∀ p1 p2, Inv p1.2 → Inv p2.2 → Inv (fJoin p1 p2).2)
    (t : NiceNode) :
    Inv (niceTreeFold fLeaf fIntro fForget fJoin t).2 := by
  induction t with
  | leaf => exact h_leaf
  | introduce v child ih => exact h_intro v _ ih
  | forget v child ih => exact h_forget v _ ih
  | join left right ihl ihr => exact h_join _ _ ihl ihr

/-! ## Lower bound preservation (KEY theorem for DP) -/

/-- If each operation of the DP gives results <= the corresponding cost,
    then the full DP gives a lower bound on the cost function. -/
theorem niceTreeFold_lower_bound
    (fLeaf : Nat) (fIntro : Nat → Nat → Nat)
    (fForget : Nat → Nat → Nat) (fJoin : Nat → Nat → Nat)
    (costLeaf : Nat) (costIntro : Nat → Nat → Nat)
    (costForget : Nat → Nat → Nat) (costJoin : Nat → Nat → Nat)
    (h_leaf : fLeaf ≤ costLeaf)
    (h_intro : ∀ v r c, r ≤ c → fIntro v r ≤ costIntro v c)
    (h_forget : ∀ v r c, r ≤ c → fForget v r ≤ costForget v c)
    (h_join : ∀ r1 r2 c1 c2, r1 ≤ c1 → r2 ≤ c2 → fJoin r1 r2 ≤ costJoin c1 c2)
    (t : NiceNode) :
    niceTreeFold fLeaf fIntro fForget fJoin t
      ≤ niceTreeFold costLeaf costIntro costForget costJoin t := by
  induction t with
  | leaf => exact h_leaf
  | introduce v child ih => exact h_intro v _ _ ih
  | forget v child ih => exact h_forget v _ _ ih
  | join left right ihl ihr => exact h_join _ _ _ _ ihl ihr

/-! ## Structural properties of niceTreeFold -/

theorem niceTreeFold_leaf {β : Type} (fLeaf : β) (fIntro : Nat → β → β)
    (fForget : Nat → β → β) (fJoin : β → β → β) :
    niceTreeFold fLeaf fIntro fForget fJoin .leaf = fLeaf := rfl

theorem niceTreeFold_intro {β : Type} (fLeaf : β) (fIntro : Nat → β → β)
    (fForget : Nat → β → β) (fJoin : β → β → β) (v : Nat) (child : NiceNode) :
    niceTreeFold fLeaf fIntro fForget fJoin (.introduce v child)
      = fIntro v (niceTreeFold fLeaf fIntro fForget fJoin child) := rfl

theorem niceTreeFold_forget {β : Type} (fLeaf : β) (fIntro : Nat → β → β)
    (fForget : Nat → β → β) (fJoin : β → β → β) (v : Nat) (child : NiceNode) :
    niceTreeFold fLeaf fIntro fForget fJoin (.forget v child)
      = fForget v (niceTreeFold fLeaf fIntro fForget fJoin child) := rfl

theorem niceTreeFold_join {β : Type} (fLeaf : β) (fIntro : Nat → β → β)
    (fForget : Nat → β → β) (fJoin : β → β → β) (l r : NiceNode) :
    niceTreeFold fLeaf fIntro fForget fJoin (.join l r)
      = fJoin (niceTreeFold fLeaf fIntro fForget fJoin l)
              (niceTreeFold fLeaf fIntro fForget fJoin r) := rfl

/-- Size of NiceNode is always positive. -/
theorem niceNode_size_pos (t : NiceNode) : 0 < t.size := by
  cases t <;> simp [NiceNode.size] <;> omega

/-! ## Concrete fold: count nodes by type -/

def countIntroduce : NiceNode → Nat :=
  niceTreeFold 0 (fun _ r => 1 + r) (fun _ r => r) (fun r1 r2 => r1 + r2)

def countForget : NiceNode → Nat :=
  niceTreeFold 0 (fun _ r => r) (fun _ r => 1 + r) (fun r1 r2 => r1 + r2)

def countJoin : NiceNode → Nat :=
  niceTreeFold 0 (fun _ r => r) (fun _ r => r) (fun r1 r2 => 1 + r1 + r2)

def countNodes : NiceNode → Nat :=
  niceTreeFold 1 (fun _ r => 1 + r) (fun _ r => 1 + r) (fun r1 r2 => 1 + r1 + r2)

theorem countNodes_eq_size (t : NiceNode) : countNodes t = t.size := by
  induction t with
  | leaf => rfl
  | introduce v child ih =>
    show 1 + countNodes child = 1 + child.size; omega
  | forget v child ih =>
    show 1 + countNodes child = 1 + child.size; omega
  | join left right ihl ihr =>
    show 1 + countNodes left + countNodes right = 1 + left.size + right.size; omega

-- ============================================================
-- Part 2: Per-vertex cost functions (from TrustHash/DP/CryptoCost.lean)
-- ============================================================

/-! ## Per-vertex cost functions

In the DP over nice tree decompositions, each vertex in a bag
represents an S-box or constraint. The cost of "activating" a vertex
depends on the attack type:
- Differential: each active S-box contributes factor delta
- Algebraic: each vertex in the treewidth bag contributes factor d -/

/-- Cost parameters for a single vertex in the DP. -/
structure VertexCostParams where
  delta : Nat  -- differential uniformity of the S-box
  degree : Nat -- algebraic degree of the S-box
  h_delta : delta ≥ 1
  h_degree : degree ≥ 1

/-- Differential cost of activating a single S-box vertex. -/
def vertexDiffCost (p : VertexCostParams) : Nat := p.delta

/-- Algebraic cost of a vertex in the treewidth bag. -/
def vertexAlgCost (p : VertexCostParams) : Nat := p.degree

/-! ## Additive cost over bags -/

/-- Additive cost: sum of cost function over a list of vertices. -/
def additiveCost (f : Nat → Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => f x + additiveCost f xs

@[simp] theorem additiveCost_nil (f : Nat → Nat) : additiveCost f [] = 0 := rfl

@[simp] theorem additiveCost_cons (f : Nat → Nat) (x : Nat) (xs : List Nat) :
    additiveCost f (x :: xs) = f x + additiveCost f xs := rfl

/-- Cost decomposition: cost over append = sum of costs. -/
theorem additiveCost_append (f : Nat → Nat) (l₁ l₂ : List Nat) :
    additiveCost f (l₁ ++ l₂) = additiveCost f l₁ + additiveCost f l₂ := by
  induction l₁ with
  | nil => simp [additiveCost]
  | cons x xs ih =>
    simp only [List.cons_append, additiveCost, ih]
    omega

/-- Pointwise bound implies total bound. -/
theorem additiveCost_le_of_pointwise (f g : Nat → Nat) (l : List Nat)
    (h : ∀ x, x ∈ l → f x ≤ g x) :
    additiveCost f l ≤ additiveCost g l := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    simp only [additiveCost]
    exact Nat.add_le_add (h x (List.Mem.head xs))
      (ih (fun y hy => h y (List.Mem.tail x hy)))

/-- Zero function gives zero cost. -/
theorem additiveCost_zero (l : List Nat) :
    additiveCost (fun _ => 0) l = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [additiveCost, ih]

/-- Constant function: total = length * constant. -/
theorem additiveCost_const (c : Nat) (l : List Nat) :
    additiveCost (fun _ => c) l = l.length * c := by
  induction l with
  | nil => simp [additiveCost]
  | cons x xs ih =>
    simp only [additiveCost, List.length_cons, ih, Nat.add_mul, Nat.one_mul]
    omega

/-! ## Bag cost for nice trees -/

/-- Cost of a bag under a uniform per-vertex cost function. -/
def bagCost (costPerVertex : Nat) (bag : List Nat) : Nat :=
  bag.length * costPerVertex

theorem bagCost_eq_additiveCost (c : Nat) (bag : List Nat) :
    bagCost c bag = additiveCost (fun _ => c) bag := by
  simp [bagCost, additiveCost_const]

theorem bagCost_monotone (c₁ c₂ : Nat) (bag : List Nat) (h : c₁ ≤ c₂) :
    bagCost c₁ bag ≤ bagCost c₂ bag := by
  simp [bagCost]
  exact Nat.mul_le_mul_left bag.length h

theorem bagCost_nil (c : Nat) : bagCost c [] = 0 := by simp [bagCost]

theorem bagCost_singleton (c : Nat) (v : Nat) : bagCost c [v] = c := by
  simp [bagCost]

/-! ## Exponential attack cost from bag -/

/-- Exponential cost: base^(bag size). Models the real attack complexity. -/
def expBagCost (base : Nat) (bag : List Nat) : Nat :=
  base ^ bag.length

theorem expBagCost_monotone (b₁ b₂ : Nat) (bag : List Nat) (h : b₁ ≤ b₂) :
    expBagCost b₁ bag ≤ expBagCost b₂ bag := by
  simp [expBagCost]
  exact Nat.pow_le_pow_left h bag.length

theorem expBagCost_nil (b : Nat) : expBagCost b [] = 1 := by
  simp [expBagCost]

theorem expBagCost_base_one (bag : List Nat) : expBagCost 1 bag = 1 := by
  simp [expBagCost, Nat.one_pow]

-- ============================================================
-- Part 3: DPOperations (from TrustHash/DP/DPOperations.lean)
-- ============================================================

/-! ## DP State

The DP computes minimum attack cost bottom-up through the nice tree.
At each node, the state is a Nat representing the accumulated cost. -/

/-- DP leaf: base cost before any vertices are considered. -/
def dpLeaf : Nat := 1

/-- DP introduce: add vertex cost to accumulated cost. -/
def dpIntroduce (costPerVertex : Nat) (_ : Nat) (childResult : Nat) : Nat :=
  childResult + costPerVertex

/-- DP forget: minimize over vertex assignment (simplified: identity). -/
def dpForget (_ : Nat) (childResult : Nat) : Nat :=
  childResult

/-- DP join: combine two independent subtree costs. -/
def dpJoin (leftResult rightResult : Nat) : Nat :=
  leftResult + rightResult

/-! ## Full DP via niceTreeFold -/

/-- Run the full DP over a nice tree with uniform vertex cost. -/
def cryptoDP (costPerVertex : Nat) (tree : NiceNode) : Nat :=
  niceTreeFold dpLeaf (dpIntroduce costPerVertex) dpForget dpJoin tree

/-! ## Cost function (upper bound) via niceTreeFold -/

def costLeaf : Nat := 1
def costIntroduce (costPerVertex : Nat) (_ : Nat) (childCost : Nat) : Nat :=
  childCost + costPerVertex
def costForget (_ : Nat) (childCost : Nat) : Nat := childCost
def costJoin (leftCost rightCost : Nat) : Nat := leftCost + rightCost

def treeCost (costPerVertex : Nat) (tree : NiceNode) : Nat :=
  niceTreeFold costLeaf (costIntroduce costPerVertex) costForget costJoin tree

/-! ## DP = Cost (tight bound) -/

theorem dp_eq_cost_intro (c v : Nat) (r : Nat) :
    dpIntroduce c v r = costIntroduce c v r := rfl

theorem dp_eq_cost_forget (v : Nat) (r : Nat) :
    dpForget v r = costForget v r := rfl

theorem dp_eq_cost_join (r1 r2 : Nat) :
    dpJoin r1 r2 = costJoin r1 r2 := rfl

theorem cryptoDP_eq_treeCost (c : Nat) (tree : NiceNode) :
    cryptoDP c tree = treeCost c tree := rfl

/-! ## Lower bound preservation -/

theorem introduce_preserves_bound (c : Nat) (v : Nat) (r_dp r_cost : Nat)
    (h : r_dp ≤ r_cost) :
    dpIntroduce c v r_dp ≤ costIntroduce c v r_cost := by
  simp [dpIntroduce, costIntroduce]; omega

theorem forget_preserves_bound (v : Nat) (r_dp r_cost : Nat)
    (h : r_dp ≤ r_cost) :
    dpForget v r_dp ≤ costForget v r_cost := by
  simp [dpForget, costForget]; exact h

theorem join_preserves_bound (l_dp r_dp l_cost r_cost : Nat)
    (hl : l_dp ≤ l_cost) (hr : r_dp ≤ r_cost) :
    dpJoin l_dp r_dp ≤ costJoin l_cost r_cost := by
  simp [dpJoin, costJoin]; exact Nat.add_le_add hl hr

theorem cryptoDP_lower_bound (c : Nat) (tree : NiceNode) :
    cryptoDP c tree ≤ treeCost c tree := by
  apply niceTreeFold_lower_bound
  · exact Nat.le_refl _
  · intro v r_dp r_cost h; exact introduce_preserves_bound c v r_dp r_cost h
  · intro v r_dp r_cost h; exact forget_preserves_bound v r_dp r_cost h
  · intro l_dp r_dp l_cost r_cost hl hr; exact join_preserves_bound l_dp r_dp l_cost r_cost hl hr

/-! ## Invariant preservation -/

theorem cryptoDP_pos (c : Nat) (hc : c ≥ 1) (tree : NiceNode) :
    cryptoDP c tree ≥ 1 := by
  apply niceTreeFold_inv (P := fun r => r ≥ 1)
  · exact Nat.le_refl _
  · intro _ r hr; simp [dpIntroduce]; omega
  · intro _ r hr; simp [dpForget]; exact hr
  · intro r1 r2 h1 _; simp [dpJoin]; omega

/-! ## Monotonicity -/

theorem cryptoDP_monotone (c₁ c₂ : Nat) (h : c₁ ≤ c₂) (tree : NiceNode) :
    cryptoDP c₁ tree ≤ cryptoDP c₂ tree := by
  apply niceTreeFold_lower_bound
  · exact Nat.le_refl _
  · intro v r1 r2 hr; simp [dpIntroduce]; omega
  · intro v r1 r2 hr; simp [dpForget]; exact hr
  · intro l1 r1 l2 r2 hl hr; simp [dpJoin]; exact Nat.add_le_add hl hr

-- ============================================================
-- Part 4: SecurityDP (from TrustHash/DP/SecurityDP.lean)
-- ============================================================

/-- Differential attack DP: each vertex costs delta. -/
def differentialDP (delta : Nat) (tree : NiceNode) : Nat :=
  cryptoDP delta tree

/-- Algebraic attack DP: each vertex costs degree. -/
def algebraicDP (degree : Nat) (tree : NiceNode) : Nat :=
  cryptoDP degree tree

/-- Security DP: minimum of differential and algebraic DPs. -/
def securityDP (delta degree : Nat) (tree : NiceNode) : Nat :=
  min (differentialDP delta tree) (algebraicDP degree tree)

/-! ## SecurityDP positivity -/

theorem differentialDP_pos (delta : Nat) (hd : delta ≥ 1) (tree : NiceNode) :
    differentialDP delta tree ≥ 1 := cryptoDP_pos delta hd tree

theorem algebraicDP_pos (degree : Nat) (hd : degree ≥ 1) (tree : NiceNode) :
    algebraicDP degree tree ≥ 1 := cryptoDP_pos degree hd tree

theorem securityDP_pos (delta degree : Nat) (hd : delta ≥ 1) (hdeg : degree ≥ 1)
    (tree : NiceNode) : securityDP delta degree tree ≥ 1 := by
  simp only [securityDP, Nat.min_def]
  split
  · exact differentialDP_pos delta hd tree
  · exact algebraicDP_pos degree hdeg tree

/-! ## SecurityDP monotonicity -/

theorem differentialDP_monotone (d₁ d₂ : Nat) (h : d₁ ≤ d₂) (tree : NiceNode) :
    differentialDP d₁ tree ≤ differentialDP d₂ tree := cryptoDP_monotone d₁ d₂ h tree

theorem algebraicDP_monotone (d₁ d₂ : Nat) (h : d₁ ≤ d₂) (tree : NiceNode) :
    algebraicDP d₁ tree ≤ algebraicDP d₂ tree := cryptoDP_monotone d₁ d₂ h tree

theorem securityDP_monotone (d₁ d₂ g₁ g₂ : Nat)
    (hd : d₁ ≤ d₂) (hg : g₁ ≤ g₂) (tree : NiceNode) :
    securityDP d₁ g₁ tree ≤ securityDP d₂ g₂ tree := by
  have h1 := differentialDP_monotone d₁ d₂ hd tree
  have h2 := algebraicDP_monotone g₁ g₂ hg tree
  simp only [securityDP, Nat.min_def]
  split <;> split <;> omega

/-! ## SecurityDP lower bounds -/

theorem differentialDP_lower_bound (delta : Nat) (tree : NiceNode) :
    differentialDP delta tree ≤ treeCost delta tree := cryptoDP_lower_bound delta tree

theorem algebraicDP_lower_bound (degree : Nat) (tree : NiceNode) :
    algebraicDP degree tree ≤ treeCost degree tree := cryptoDP_lower_bound degree tree

/-! ## DP cost formula -/

def dpCostFormula (c : Nat) (tree : NiceNode) : Nat :=
  1 + countIntroduce tree * c

theorem dpCostFormula_leaf (c : Nat) :
    dpCostFormula c .leaf = cryptoDP c .leaf := by
  simp [dpCostFormula, countIntroduce, niceTreeFold, cryptoDP, dpLeaf]

theorem dpCostFormula_intro_chain (c : Nat) (v : Nat) :
    dpCostFormula c (.introduce v .leaf) = 1 + c := by
  simp [dpCostFormula, countIntroduce, niceTreeFold]

/-! ## Concrete validation -/

private def tree1' : NiceNode := .introduce 0 (.introduce 1 .leaf)
private def tree2' : NiceNode := .join (.introduce 0 .leaf) (.introduce 1 .leaf)
private def tree3' : NiceNode :=
  .forget 2 (.join (.introduce 0 (.introduce 2 .leaf))
                    (.introduce 1 (.introduce 2 .leaf)))

theorem dp_tree1 : cryptoDP 3 tree1' = 7 := by native_decide
theorem dp_tree2 : cryptoDP 3 tree2' = 8 := by native_decide
theorem dp_tree3 : cryptoDP 2 tree3' = 10 := by native_decide
theorem dp_lower_bound_concrete : cryptoDP 3 tree2' ≤ treeCost 3 tree2' := by native_decide
theorem dp_monotone_concrete : cryptoDP 2 tree2' ≤ cryptoDP 5 tree2' := by native_decide
theorem dp_leaf_zero : cryptoDP 0 .leaf = 1 := by native_decide
theorem dp_pos_concrete : cryptoDP 1 tree2' ≥ 1 := by native_decide

-- SecurityDP validation
theorem diffDP_simple : differentialDP 4 tree1' = 9 := by native_decide
theorem algDP_join : algebraicDP 3 tree2' = 8 := by native_decide
theorem secDP_join_val : securityDP 4 3 tree2' = 8 := by native_decide
theorem secDP_complex : securityDP 4 3 tree3' = 14 := by native_decide

-- NiceTree fold validation
theorem ex1_count_intro : countIntroduce tree1' = 2 := by native_decide
theorem ex2_count_join : countJoin tree2' = 1 := by native_decide
theorem ex3_count_forget : countForget tree3' = 1 := by native_decide
theorem ex3_count_intro : countIntroduce tree3' = 4 := by native_decide
theorem ex3_count_eq_size : countNodes tree3' = tree3'.size := by native_decide

-- Additive cost validation
theorem additive_cost_ex :
    additiveCost (fun x => x) [2, 3, 5] = 10 := by native_decide
theorem bag_cost_ex : bagCost 3 [0, 1, 2, 3] = 12 := by native_decide
theorem exp_bag_cost_ex : expBagCost 4 [0, 1, 2] = 64 := by native_decide

end SuperHash.Graph.CryptoCost
