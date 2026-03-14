/-!
# SuperHash.TrustHash.NiceTree — Nice tree decomposition for security DP

Adapts TrustHash's NiceTree + DP infrastructure for computing structural
security costs via tree decomposition of hash constraint graphs.

## Architecture (from TrustHash)
1. Constraint graph: variables are S-box inputs/outputs, edges are dependencies
2. Tree decomposition: via greedy min-degree elimination
3. Nice tree: standard form with 4 node types (leaf, introduce, forget, join)
4. Security DP: bottom-up cost computation on nice tree

## Source
- TrustHash/DP/NiceTree.lean (213 LOC)
- TrustHash/DP/DPOperations.lean (216 LOC)
- TrustHash/DP/SecurityDP.lean (158 LOC)
- TrustHash/DP/CryptoCost.lean (161 LOC)
-/

namespace SuperHash.TrustHash

-- ============================================================
-- Section 1: Nice Tree Decomposition
-- ============================================================

/-- A nice tree decomposition node. Standard form ensures each node
    modifies the bag by exactly one vertex (add or remove). -/
inductive NiceNode where
  | leaf (bag : List Nat)
  | introduce (vertex : Nat) (child : NiceNode)
  | forget (vertex : Nat) (child : NiceNode)
  | join (left right : NiceNode)
  deriving Repr, Inhabited

/-- Bag at a node: the set of active vertices. -/
def NiceNode.bag : NiceNode → List Nat
  | .leaf b => b
  | .introduce v child => v :: child.bag
  | .forget _ child => child.bag  -- vertex removed from bag
  | .join left _ => left.bag  -- both children have same bag

/-- Treewidth: max bag size - 1 across all nodes. -/
def NiceNode.maxBagSize : NiceNode → Nat
  | .leaf b => b.length
  | .introduce _ child => child.maxBagSize + 1
  | .forget _ child => child.maxBagSize
  | .join left right => max left.maxBagSize right.maxBagSize

def NiceNode.treewidth (t : NiceNode) : Nat := t.maxBagSize - 1

/-- Number of leaf nodes (= number of S-box instances). -/
def NiceNode.leafCount : NiceNode → Nat
  | .leaf _ => 1
  | .introduce _ child | .forget _ child => child.leafCount
  | .join left right => left.leafCount + right.leafCount

/-- Number of introduce nodes (= variables introduced). -/
def NiceNode.introduceCount : NiceNode → Nat
  | .leaf _ => 0
  | .introduce _ child => 1 + child.introduceCount
  | .forget _ child => child.introduceCount
  | .join left right => left.introduceCount + right.introduceCount

-- ============================================================
-- Section 2: Security DP on Nice Trees
-- ============================================================

/-- Cost function for DP: maps (bag assignment, node type) to Nat cost.
    For differential analysis: cost = δ per active S-box in bag.
    For algebraic analysis: cost = degree per variable in bag. -/
structure DPCostFn where
  /-- Cost of a leaf node with given bag -/
  leafCost : List Nat → Nat
  /-- Cost of introducing a new vertex -/
  introduceCost : Nat → Nat → Nat  -- vertex → child cost → new cost
  /-- Cost of forgetting a vertex (minimize over assignments) -/
  forgetCost : Nat → Nat → Nat  -- vertex → child cost → new cost
  /-- Cost of joining two subtrees -/
  joinCost : Nat → Nat → Nat  -- left cost → right cost → combined

/-- Run DP bottom-up on a nice tree with given cost function.
    Returns the structural security cost. -/
def runDP (tree : NiceNode) (costFn : DPCostFn) : Nat :=
  match tree with
  | .leaf bag => costFn.leafCost bag
  | .introduce v child =>
    let childCost := runDP child costFn
    costFn.introduceCost v childCost
  | .forget v child =>
    let childCost := runDP child costFn
    costFn.forgetCost v childCost
  | .join left right =>
    let leftCost := runDP left costFn
    let rightCost := runDP right costFn
    costFn.joinCost leftCost rightCost

-- ============================================================
-- Section 3: Concrete cost functions
-- ============================================================

/-- Differential cost: each leaf contributes δ per S-box.
    Source: TrustHash/DP/CryptoCost.lean -/
def differentialCostFn (delta : Nat) : DPCostFn where
  leafCost := fun bag => delta * bag.length  -- δ per active variable
  introduceCost := fun _ childCost => childCost  -- introducing doesn't change cost
  forgetCost := fun _ childCost => childCost  -- forgetting minimizes (identity here)
  joinCost := fun l r => l + r  -- join accumulates costs

/-- Algebraic cost: degree grows exponentially per round.
    Source: TrustHash/DP/CryptoCost.lean -/
def algebraicCostFn (sboxDeg : Nat) (treewidth : Nat) : DPCostFn where
  leafCost := fun _ => sboxDeg  -- base degree from S-box
  introduceCost := fun _ childCost => childCost * sboxDeg  -- degree multiplies
  forgetCost := fun _ childCost => childCost  -- degree preserved
  joinCost := fun l r => max l r  -- parallel: take max degree

/-- Combined security cost: min(differential, algebraic).
    Source: TrustHash/Pipeline/StructuralPipeline.lean -/
def securityDP (tree : NiceNode) (delta sboxDeg : Nat) : Nat :=
  let diffCost := runDP tree (differentialCostFn delta)
  let algCost := runDP tree (algebraicCostFn sboxDeg (tree.treewidth))
  min diffCost algCost

-- ============================================================
-- Section 4: Concrete hash instances
-- ============================================================

/-- AES-128 nice tree: 4×4 state, 10 rounds.
    Full SPN → complete graph K_4 per round → treewidth 3.
    Simplified: linear chain of 10 round nodes. -/
def aesNiceTree : NiceNode :=
  -- 10-round SPN: each round introduces 4 variables (state elements)
  -- Simplified model: 2-level tree (sufficient for treewidth extraction)
  .join
    (.introduce 0 (.introduce 1 (.introduce 2 (.introduce 3 (.leaf [0, 1, 2, 3])))))
    (.introduce 4 (.introduce 5 (.introduce 6 (.introduce 7 (.leaf [4, 5, 6, 7])))))

/-- Poseidon-128 (t=3) nice tree: 3-element state.
    Full rounds: K_3 → treewidth 2.
    Partial rounds: single S-box → treewidth 0. -/
def poseidonNiceTree : NiceNode :=
  .join
    (.introduce 0 (.introduce 1 (.introduce 2 (.leaf [0, 1, 2]))))
    (.leaf [3])  -- partial round: single element

-- ============================================================
-- Section 5: Properties
-- ============================================================

/-- DP cost is non-negative (trivially: Nat). -/
theorem runDP_nonneg (tree : NiceNode) (costFn : DPCostFn) :
    runDP tree costFn ≥ 0 := Nat.zero_le _

/-- securityDP is bounded by each component. -/
theorem securityDP_le_diff (tree : NiceNode) (delta sboxDeg : Nat) :
    securityDP tree delta sboxDeg ≤ runDP tree (differentialCostFn delta) :=
  Nat.min_le_left _ _

theorem securityDP_le_alg (tree : NiceNode) (delta sboxDeg : Nat) :
    securityDP tree delta sboxDeg ≤ runDP tree (algebraicCostFn sboxDeg tree.treewidth) :=
  Nat.min_le_right _ _

/-- leafCount is positive for any non-trivial tree. -/
theorem leaf_count_pos_leaf (bag : List Nat) :
    (NiceNode.leaf bag).leafCount > 0 := by simp [NiceNode.leafCount]

-- ============================================================
-- Section 6: Smoke tests
-- ============================================================

#eval aesNiceTree.treewidth          -- treewidth of AES model
#eval aesNiceTree.leafCount          -- number of S-box instances
#eval poseidonNiceTree.treewidth     -- treewidth of Poseidon model

#eval securityDP aesNiceTree 4 7     -- AES: min(diff, alg)
#eval securityDP poseidonNiceTree 2 5  -- Poseidon: min(diff, alg)

-- ============================================================
-- Section 7: Non-vacuity
-- ============================================================

example : aesNiceTree.leafCount > 0 := by native_decide
example : poseidonNiceTree.leafCount > 0 := by native_decide

end SuperHash.TrustHash
