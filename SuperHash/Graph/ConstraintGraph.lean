/-
  SuperHash/Graph/ConstraintGraph.lean
  Build constraint graph from cipher parameters

  The constraint graph encodes variable dependencies in the SPN round function:
  - **Full rounds**: MDS mixing creates all-to-all dependencies -> complete graph K_t
  - **Partial rounds**: Only 1 S-box active -> star graph S_t (center = cell 0)
  - **HADES structure** (mixed): Full rounds dominate -> K_t

  This graph feeds into `fromGraph` (NiceTreeConvert) to produce a NiceNode
  for DP-based security analysis.

  Adapted from TrustHash/ConstraintGraph.lean (153 LOC, 0 sorry).
  ZERO HashOp dependency -- uses local CipherParams instead of HashSpec.

  References:
  - Grassi et al. 2019: HADES design strategy (full + partial rounds)
  - Daemen-Rijmen 2002: Wide trail strategy (MDS -> complete mixing)
-/

import SuperHash.Graph.SimpleGraph

namespace SuperHash.Graph.ConstraintGraph

open SuperHash.Graph

/-! ## Cipher Parameters (local, no HashSpec dependency)

Minimal specification needed to build a constraint graph. -/

/-- Minimal cipher specification for constraint graph construction. -/
structure CipherParams where
  stateWidth : Nat    -- number of state words (e.g. 3 for Poseidon, 4 for AES)
  fullRounds : Nat    -- number of full SPN rounds
  partialRounds : Nat -- number of partial rounds (HADES-style)
  deriving Repr, BEq, DecidableEq

/-! ## Standard cipher instances -/

/-- Poseidon-128 (t=3): 8 full + 57 partial rounds. -/
def poseidon128 : CipherParams := { stateWidth := 3, fullRounds := 8, partialRounds := 57 }

/-- AES-128 (t=4): 10 full rounds, no partial. -/
def aes128 : CipherParams := { stateWidth := 4, fullRounds := 10, partialRounds := 0 }

/-- SHA-256 model (t=8): all full rounds. -/
def sha256Model : CipherParams := { stateWidth := 8, fullRounds := 64, partialRounds := 0 }

/-- Keccak-256 model (t=5): all full rounds. -/
def keccak256Model : CipherParams := { stateWidth := 5, fullRounds := 24, partialRounds := 0 }

/-- Rescue-Prime (t=3): all full rounds. -/
def rescuePrime : CipherParams := { stateWidth := 3, fullRounds := 22, partialRounds := 0 }

/-- Weak hash (t=2): minimal. -/
def weakHash : CipherParams := { stateWidth := 2, fullRounds := 4, partialRounds := 0 }

/-! ## Constraint Graph Construction

The constraint graph of an SPN hash function captures variable dependencies
introduced by the round function components:

1. **S-box layer**: Each S-box operates on a single state word -> no cross-word edges
2. **MDS mixing layer**: Multiplies all state words by MDS matrix -> all-to-all edges
3. **Round constant addition**: No new dependencies (additive, same variables)

For HADES-style constructions:
- Full rounds apply S-box to ALL state words + MDS mixing -> complete graph K_t
- Partial rounds apply S-box to ONLY state word 0 + MDS mixing -> star graph S_t

The effective constraint graph is determined by the most connected section,
since treewidth is monotone: tw(G1) <= tw(G1 U G2).
-/

/-- Build the constraint graph for an SPN hash function.
    - If full rounds exist: complete graph K_t (MDS mixes all t words)
    - If only partial rounds: star graph S_t (only word 0 gets S-box)
    (Grassi et al. 2019; Daemen-Rijmen 2002) -/
def buildConstraintGraph (spec : CipherParams) : SimpleGraph :=
  if spec.fullRounds > 0 then
    completeGraph spec.stateWidth  -- Full rounds: complete K_t
  else
    starGraph spec.stateWidth      -- Partial only: star S_t

/-! ## Basic properties -/

/-- Constraint graph has stateWidth vertices. -/
theorem buildConstraintGraph_numVertices (spec : CipherParams) :
    (buildConstraintGraph spec).numVertices = spec.stateWidth := by
  unfold buildConstraintGraph
  split
  · exact completeGraph_numVertices _
  · exact starGraph_numVertices _

/-- When full rounds exist, constraint graph is the complete graph. -/
theorem buildConstraintGraph_complete (spec : CipherParams)
    (h : spec.fullRounds > 0) :
    buildConstraintGraph spec = completeGraph spec.stateWidth := by
  unfold buildConstraintGraph; simp [h]

/-- When no full rounds, constraint graph is the star graph. -/
theorem buildConstraintGraph_star (spec : CipherParams)
    (h : spec.fullRounds = 0) :
    buildConstraintGraph spec = starGraph spec.stateWidth := by
  unfold buildConstraintGraph; simp [h]

/-! ## Treewidth consistency

The constraint graph's treewidth should match the analytical formula:
- K_t has treewidth t-1 (complete graph)
- S_t has treewidth 1 (star graph -> path decomposition) -/

/-- Complete graph K_3 has max degree 2 (= t-1). -/
theorem complete3_maxDegree : maxDegree (completeGraph 3) = 2 := by native_decide

/-- Complete graph K_4 has max degree 3 (= t-1). -/
theorem complete4_maxDegree : maxDegree (completeGraph 4) = 3 := by native_decide

/-- Complete graph K_5 has max degree 4 (= t-1). -/
theorem complete5_maxDegree : maxDegree (completeGraph 5) = 4 := by native_decide

/-- Complete graph K_8 has max degree 7 (= t-1). -/
theorem complete8_maxDegree : maxDegree (completeGraph 8) = 7 := by native_decide

/-- Star graph S_3 has max degree 2 (center vertex). -/
theorem star3_maxDegree : maxDegree (starGraph 3) = 2 := by native_decide

/-- Star graph S_4 has max degree 3 (center vertex). -/
theorem star4_maxDegree : maxDegree (starGraph 4) = 3 := by native_decide

/-! ## Concrete validations (native_decide) -/

/-- Poseidon (t=3): constraint graph is K_3 with 3 edges. -/
theorem poseidon_graph_edges :
    numEdges (buildConstraintGraph poseidon128) = 3 := by native_decide

/-- Poseidon (t=3): constraint graph has 3 vertices. -/
theorem poseidon_graph_vertices :
    (buildConstraintGraph poseidon128).numVertices = 3 := by native_decide

/-- AES (t=4): constraint graph is K_4 with 6 edges. -/
theorem aes_graph_edges :
    numEdges (buildConstraintGraph aes128) = 6 := by native_decide

/-- AES (t=4): constraint graph has 4 vertices. -/
theorem aes_graph_vertices :
    (buildConstraintGraph aes128).numVertices = 4 := by native_decide

/-- SHA-256 model (t=8): constraint graph is K_8 with 28 edges. -/
theorem sha256_graph_edges :
    numEdges (buildConstraintGraph sha256Model) = 28 := by native_decide

/-- Keccak model (t=5): constraint graph is K_5 with 10 edges. -/
theorem keccak_graph_edges :
    numEdges (buildConstraintGraph keccak256Model) = 10 := by native_decide

/-- Rescue-Prime (t=3): constraint graph is K_3 with 3 edges. -/
theorem rescue_graph_edges :
    numEdges (buildConstraintGraph rescuePrime) = 3 := by native_decide

/-- Weak hash (t=2): constraint graph is K_2 with 1 edge. -/
theorem weak_graph_edges :
    numEdges (buildConstraintGraph weakHash) = 1 := by native_decide

/-- Complete graph K_3 edge count. -/
theorem k3_edges : numEdges (completeGraph 3) = 3 := by native_decide

/-- Complete graph K_9 edge count = 9*8/2 = 36. -/
theorem k9_edges : numEdges (completeGraph 9) = 36 := by native_decide

end SuperHash.Graph.ConstraintGraph
