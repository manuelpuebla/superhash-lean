import SuperHash.Graph.Util.NatOpt
import SuperHash.Graph.NiceTreeConvert
/-!
# SuperHash.Graph.TreewidthDP -- Exponential DP on Nice Tree Decompositions

Exponential-time DP that enumerates all k^tw possible bag assignments.
Produces optimal (minimum cost) attack complexity for given treewidth.

Adapted from TrustHash/DP/TreewidthDP.lean (407 LOC, 0 sorry).
Parametric over cost configuration (not coupled to EGraph types).
Uses List-based DPTable for proof tractability.

## Main Definitions

* `DPConfig` -- parametric cost configuration (numStates, vertexCost)
* `BagAssignment` -- partial assignment of vertex states in a bag
* `DPTable` -- maps bag assignments to minimum costs (List-backed)
* `dpLeaf/dpIntroduce/dpForget/dpJoin` -- four DP operations
* `runDP` -- bottom-up DP on NiceNode (structural recursion)
* `DPCompleteInv` -- completeness + cost bound invariant
* `DPOptimalityWitness` -- certifies DP produces optimal cost

## References

* Goharshady et al. 2024, "Fast and Optimal Extraction for Sparse Equality Graphs"
* Arnborg et al. 1991 (DP on tree decompositions)
-/

namespace SuperHash.Graph.TreewidthDP

open SuperHash.Graph.NiceTreeConvert

/-! ## BagAssignment -/

/-- A bag assignment maps each vertex in the current bag to a state (0..k-1).
    Stored as a sorted list of (vertexId, state) pairs for canonical comparison. -/
abbrev BagAssignment := List (Nat × Nat)

/-- Total order for canonical sorting of bag assignments. -/
def bagEntryLe (a b : Nat × Nat) : Bool :=
  a.1 < b.1 || (a.1 == b.1 && decide (a.2 ≤ b.2))

/-- Canonicalize a bag assignment by sorting. Idempotent. -/
def canonicalize (ba : BagAssignment) : BagAssignment :=
  ba.mergeSort bagEntryLe

/-! ## DPConfig -/

/-- Configuration for the exponential DP engine.
    Parametric over number of states per vertex and cost function. -/
structure DPConfig where
  /-- Number of possible states per vertex (e.g. 2 for active/inactive). -/
  numStates : Nat
  /-- Cost of assigning state `s` to vertex `v`. -/
  vertexCost : Nat → Nat → Nat
  /-- States must be non-empty. -/
  h_pos : numStates > 0

/-! ## DPTable (List-backed for proof tractability) -/

/-- DP table: maps partial bag assignments to minimum costs.
    All keys are stored in canonical (sorted) form. Unique keys. -/
structure DPTable where
  entries : List (BagAssignment × Nat)

instance : Inhabited DPTable := ⟨⟨[]⟩⟩

namespace DPTable

/-- Empty DP table. -/
def empty : DPTable := ⟨[]⟩

/-- Update an existing key to its minimum value, or return the list unchanged
    with a flag indicating whether the key was found. -/
def updateMin (entries : List (BagAssignment × Nat)) (key : BagAssignment)
    (cost : Nat) : List (BagAssignment × Nat) × Bool :=
  match entries with
  | [] => ([], false)
  | (k, v) :: rest =>
    if k == key then
      ((k, Nat.min v cost) :: rest, true)
    else
      let (rest', found) := updateMin rest key cost
      ((k, v) :: rest', found)

/-- Insert or update: keep the minimum cost for a given canonical assignment. -/
def insertMin (t : DPTable) (ba : BagAssignment) (cost : Nat) : DPTable :=
  let key := canonicalize ba
  let (updated, found) := updateMin t.entries key cost
  if found then ⟨updated⟩ else ⟨(key, cost) :: t.entries⟩

/-- Look up the cost for a given assignment (canonicalized). -/
def get? (t : DPTable) (ba : BagAssignment) : Option Nat :=
  let key := canonicalize ba
  match t.entries.find? (fun (k, _) => k == key) with
  | some (_, v) => some v
  | none => none

/-- Number of entries in the table. -/
def size (t : DPTable) : Nat := t.entries.length

/-- Find the entry with minimum cost. -/
def findMin (t : DPTable) : Option (BagAssignment × Nat) :=
  t.entries.foldl (fun acc entry =>
    match acc with
    | none => some entry
    | some (_, bestCost) => if entry.2 < bestCost then some entry else acc
  ) none

end DPTable

/-! ## Four DP Operations -/

/-- Process a Leaf node: empty bag, cost 0. -/
def dpLeaf : DPTable :=
  DPTable.empty.insertMin [] 0

/-- Process an Introduce node: vertex `v` is being added to the bag.
    For each existing assignment, try all `numStates` states for `v`. -/
def dpIntroduce (config : DPConfig) (v : Nat) (childTable : DPTable) : DPTable :=
  childTable.entries.foldl (fun newTable (ba, cost) =>
    (List.range config.numStates).foldl (fun acc state =>
      let extBa := (v, state) :: ba
      let extraCost := config.vertexCost v state
      acc.insertMin extBa (cost + extraCost)
    ) newTable
  ) DPTable.empty

/-- Process a Forget node: vertex `v` is being removed from the bag.
    Projects out `v`, keeping the minimum cost. -/
def dpForget (v : Nat) (childTable : DPTable) : DPTable :=
  childTable.entries.foldl (fun newTable (ba, cost) =>
    let projected := ba.filter (fun (vid, _) => !(vid == v))
    newTable.insertMin projected cost
  ) DPTable.empty

/-- Process a Join node: combine two subtrees with identical bags.
    Combined cost = left + right - shared bag cost (avoid double-counting). -/
def dpJoin (config : DPConfig) (leftTable rightTable : DPTable) : DPTable :=
  leftTable.entries.foldl (fun newTable (ba, leftCost) =>
    match rightTable.get? ba with
    | some rightCost =>
      let bagCost := ba.foldl (fun acc (_, state) =>
        acc + config.vertexCost 0 state) 0
      let combinedCost := leftCost + rightCost - bagCost
      newTable.insertMin ba combinedCost
    | none => newTable
  ) DPTable.empty

/-! ## runDP: Bottom-up DP driver -/

/-- Run DP bottom-up on a NiceNode. Always terminates (structural recursion). -/
def runDP (config : DPConfig) : NiceNode → DPTable
  | .leaf => dpLeaf
  | .introduce v child => dpIntroduce config v (runDP config child)
  | .forget v child => dpForget v (runDP config child)
  | .join left right => dpJoin config (runDP config left) (runDP config right)

/-- Run DP with fuel (returns none if tree size exceeds fuel budget). -/
def runDPFueled (config : DPConfig) (tree : NiceNode) (fuel : Nat) :
    Option DPTable :=
  if tree.size ≤ fuel then some (runDP config tree) else none

/-! ## Cost extraction -/

/-- Extract the optimal (minimum) cost from the DP result. -/
def dpOptimalCost (table : DPTable) : Nat :=
  match table.findMin with
  | some (_, cost) => cost
  | none => 0

/-- Extract the optimal assignment from the DP result. -/
def dpOptimalSelection (table : DPTable) : Option BagAssignment :=
  match table.findMin with
  | some (ba, _) => some ba
  | none => none

/-! ## Binary (crypto) configurations -/

/-- Binary config: each vertex is active (state=1, cost) or inactive (state=0, free). -/
def binaryConfig (vertexCost : Nat → Nat) : DPConfig where
  numStates := 2
  vertexCost := fun v s => if s == 1 then vertexCost v else 0
  h_pos := by omega

/-- Uniform binary config: all active vertices cost the same. -/
def uniformBinaryConfig (cost : Nat) : DPConfig :=
  binaryConfig (fun _ => cost)

/-! ## findMin correctness -/

/-- findMin step function, extracted for proofs. -/
private def fmStep (acc : Option (BagAssignment × Nat))
    (entry : BagAssignment × Nat) : Option (BagAssignment × Nat) :=
  match acc with
  | none => some entry
  | some (_, best) => if entry.2 < best then some entry else acc

/-- findMin = foldl fmStep on entries. -/
private theorem findMin_eq_foldl (entries : List (BagAssignment × Nat)) :
    entries.foldl (fun acc entry =>
      match acc with
      | none => some entry
      | some (_, bestCost) => if entry.2 < bestCost then some entry else acc
    ) none = entries.foldl fmStep none := by
  congr 1

/-- findMin on empty table returns none. -/
theorem findMin_empty : DPTable.empty.findMin = none := rfl

/-- dpOptimalCost on empty table is 0. -/
theorem dpOptimalCost_empty : dpOptimalCost DPTable.empty = 0 := rfl

/-- If findMin = some (ba, cost), then dpOptimalCost = cost. -/
theorem dpOptimalCost_of_findMin (t : DPTable) (ba : BagAssignment) (cost : Nat)
    (h : t.findMin = some (ba, cost)) :
    dpOptimalCost t = cost := by
  simp [dpOptimalCost, h]

/-- fmStep from some preserves upper bound. -/
private theorem fmStep_preserves_bound
    (l : List (BagAssignment × Nat))
    (ba₀ : BagAssignment) (c₀ bound : Nat) (hle : c₀ ≤ bound) :
    ∃ ba' c', l.foldl fmStep (some (ba₀, c₀)) = some (ba', c') ∧ c' ≤ bound := by
  induction l generalizing ba₀ c₀ with
  | nil => exact ⟨ba₀, c₀, rfl, hle⟩
  | cons hd tl ih =>
    simp only [List.foldl_cons, fmStep]
    split
    · exact ih hd.1 hd.2 (by omega)
    · exact ih ba₀ c₀ hle

/-- If entry is in list, foldl fmStep from any acc returns cost <= entry cost. -/
private theorem fmStep_foldl_le
    (l : List (BagAssignment × Nat))
    (acc : Option (BagAssignment × Nat))
    (entry : BagAssignment × Nat) (hmem : entry ∈ l) :
    ∃ ba' c', l.foldl fmStep acc = some (ba', c') ∧ c' ≤ entry.2 := by
  induction l generalizing acc with
  | nil => exact absurd hmem List.not_mem_nil
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hmem with heq | hmem'
    · subst heq
      match acc with
      | none =>
        simp only [fmStep]
        exact fmStep_preserves_bound tl entry.1 entry.2 entry.2 (Nat.le_refl _)
      | some (ba₀, c₀) =>
        simp only [fmStep]
        split
        · exact fmStep_preserves_bound tl entry.1 entry.2 entry.2 (Nat.le_refl _)
        · exact fmStep_preserves_bound tl ba₀ c₀ entry.2 (by omega)
    · exact ih (fmStep acc hd) hmem'

/-- findMin returns cost <= any entry in the table. -/
theorem findMin_le_mem (t : DPTable) (entry : BagAssignment × Nat)
    (hmem : entry ∈ t.entries) :
    ∃ ba' c', t.findMin = some (ba', c') ∧ c' ≤ entry.2 := by
  show ∃ ba' c', t.entries.foldl _ none = some (ba', c') ∧ c' ≤ entry.2
  rw [findMin_eq_foldl]
  exact fmStep_foldl_le t.entries none entry hmem

/-! ## DPTable.get? and membership -/

/-- If get? returns some, there's a matching entry in the table. -/
theorem get?_some_mem (t : DPTable) (ba : BagAssignment) (cost : Nat)
    (h : t.get? ba = some cost) :
    ∃ entry ∈ t.entries, entry.2 = cost := by
  simp only [DPTable.get?] at h
  have hfind := h
  split at hfind
  · rename_i _ fst_ba v_nat heq_find
    simp at hfind
    exact ⟨(fst_ba, v_nat), List.mem_of_find?_eq_some heq_find, hfind⟩
  · simp at hfind

/-- dpOptimalCost <= any cost accessible via get?. -/
theorem dpOptimalCost_le_get (t : DPTable) (ba : BagAssignment) (cost : Nat)
    (h : t.get? ba = some cost) :
    dpOptimalCost t ≤ cost := by
  obtain ⟨entry, hmem, heq⟩ := get?_some_mem t ba cost h
  obtain ⟨ba', c', hfind, hle⟩ := findMin_le_mem t entry hmem
  simp [dpOptimalCost, hfind]
  omega

/-! ## DPCompleteInv: Correctness Invariant -/

/-- Combined completeness + cost bound invariant for DP tables.
    For any valid assignment of all vertices in `subtreeVertices`, the DP table
    contains a matching entry whose cost <= the assignment's total cost. -/
structure DPCompleteInv
    (config : DPConfig)
    (bagVertices subtreeVertices : List Nat)
    (table : DPTable) : Prop where
  has_bounded_entry : ∀ (assignment : Nat → Nat),
    (∀ v ∈ subtreeVertices, assignment v < config.numStates) →
    ∃ cost,
      table.get? (bagVertices.map (fun v => (v, assignment v))) = some cost ∧
      cost ≤ subtreeVertices.foldl (fun acc v =>
        acc + config.vertexCost v (assignment v)) 0

/-! ## DPOptimalityWitness -/

/-- DP optimality witness: certifies that the DP table correctly tracks
    the minimum cost over all valid selections of vertex states. -/
structure DPOptimalityWitness
    (config : DPConfig)
    (subtreeVertices : List Nat)
    (table : DPTable) : Prop where
  dp_is_lower_bound : ∀ (assignment : Nat → Nat),
    (∀ v ∈ subtreeVertices, assignment v < config.numStates) →
    dpOptimalCost table ≤
      subtreeVertices.foldl (fun acc v =>
        acc + config.vertexCost v (assignment v)) 0

/-! ## Bridge: DPCompleteInv -> DPOptimalityWitness -/

/-- DPCompleteInv at root (empty bag) implies DPOptimalityWitness. -/
theorem dpOptimalityWitness_from_completeInv
    (config : DPConfig) (subtreeVertices : List Nat) (table : DPTable)
    (hinv : DPCompleteInv config [] subtreeVertices table) :
    DPOptimalityWitness config subtreeVertices table := by
  constructor
  intro assignment hvalid
  obtain ⟨cost, hget, hle⟩ := hinv.has_bounded_entry assignment hvalid
  exact Nat.le_trans (dpOptimalCost_le_get table _ cost hget) hle

/-! ## Structural properties -/

/-- runDP on leaf produces dpLeaf. -/
theorem runDP_leaf (config : DPConfig) :
    runDP config .leaf = dpLeaf := rfl

/-- runDP on introduce. -/
theorem runDP_introduce (config : DPConfig) (v : Nat) (child : NiceNode) :
    runDP config (.introduce v child) =
      dpIntroduce config v (runDP config child) := rfl

/-- runDP on forget. -/
theorem runDP_forget (config : DPConfig) (v : Nat) (child : NiceNode) :
    runDP config (.forget v child) =
      dpForget v (runDP config child) := rfl

/-- runDP on join. -/
theorem runDP_join (config : DPConfig) (left right : NiceNode) :
    runDP config (.join left right) =
      dpJoin config (runDP config left) (runDP config right) := rfl

/-- runDPFueled with sufficient fuel equals runDP. -/
theorem runDPFueled_sufficient (config : DPConfig) (tree : NiceNode) (fuel : Nat)
    (h : tree.size ≤ fuel) :
    runDPFueled config tree fuel = some (runDP config tree) := by
  simp [runDPFueled, h]

/-- runDPFueled with insufficient fuel returns none. -/
theorem runDPFueled_insufficient (config : DPConfig) (tree : NiceNode) (fuel : Nat)
    (h : fuel < tree.size) :
    runDPFueled config tree fuel = none := by
  simp [runDPFueled]; omega

/-! ## Concrete validation -/

private def testConfig := uniformBinaryConfig 4

private def simpleTree := NiceNode.introduce 0 (NiceNode.introduce 1 NiceNode.leaf)
private def joinTree := NiceNode.join
  (NiceNode.introduce 0 NiceNode.leaf)
  (NiceNode.introduce 1 NiceNode.leaf)
private def forgetTree :=
  NiceNode.forget 0 (NiceNode.introduce 0 (NiceNode.introduce 1 NiceNode.leaf))

-- Leaf: 1 entry (empty assignment -> cost 0)
#eval (runDP testConfig .leaf).size            -- expected: 1
#eval dpOptimalCost (runDP testConfig .leaf)    -- expected: 0

-- Simple introduce chain: 2 vertices, each with 2 states
#eval (runDP testConfig simpleTree).size        -- expected: 4
#eval dpOptimalCost (runDP testConfig simpleTree)  -- expected: 0 (both inactive)

-- Join tree: two independent vertices
#eval (runDP testConfig joinTree).size
#eval dpOptimalCost (runDP testConfig joinTree)  -- expected: 0

-- Forget tree: forget v0, keep min over v0's states
#eval (runDP testConfig forgetTree).size
#eval dpOptimalCost (runDP testConfig forgetTree)

-- runDPFueled
#eval runDPFueled testConfig simpleTree 10 |>.map dpOptimalCost  -- some 0
#eval runDPFueled testConfig simpleTree 0 |>.map dpOptimalCost   -- none

end SuperHash.Graph.TreewidthDP
