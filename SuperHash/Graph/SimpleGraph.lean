-- SuperHash/Graph/SimpleGraph.lean
-- Simple undirected graph representation via adjacency lists
-- Foundation for treewidth computation and constraint graphs
-- Adapted from TrustHash/Graph.lean (155 LOC, 0 sorry)

namespace SuperHash.Graph

/-! ## SimpleGraph

An undirected graph on vertices 0..numVertices-1, represented as adjacency lists.
Edges are stored symmetrically: if j in adj[i] then i in adj[j]. -/

/-- Undirected graph with adjacency lists. `adj[i]` is the list of
    neighbors of vertex `i`. Invariant: symmetric and loop-free. -/
structure SimpleGraph where
  numVertices : Nat
  adj : Array (List Nat)
  h_size : adj.size = numVertices

/-- The empty graph on n vertices with no edges. -/
def emptyGraph (n : Nat) : SimpleGraph where
  numVertices := n
  adj := Array.replicate n []
  h_size := by simp

/-- Degree of vertex v (number of neighbors). -/
def degree (g : SimpleGraph) (v : Nat) (hv : v < g.numVertices) : Nat :=
  (g.adj[v]'(g.h_size ▸ hv)).length

/-- All neighbors of vertex v. -/
def neighbors (g : SimpleGraph) (v : Nat) (hv : v < g.numVertices) : List Nat :=
  g.adj[v]'(g.h_size ▸ hv)

/-- Check if edge (u, v) exists. -/
def hasEdge (g : SimpleGraph) (u v : Nat) : Bool :=
  if hu : u < g.numVertices then
    (g.adj[u]'(g.h_size ▸ hu)).contains v
  else false

/-- Number of edges (counting each edge once). Sum of degrees divided by 2. -/
def numEdges (g : SimpleGraph) : Nat :=
  let totalDeg := g.adj.foldl (fun acc nbrs => acc + nbrs.length) 0
  totalDeg / 2

/-! ## Graph construction -/

/-- Add an undirected edge between u and v (no-op if out of range or self-loop). -/
def addEdge (g : SimpleGraph) (u v : Nat) : SimpleGraph :=
  if hu : u < g.numVertices then
    if hv : v < g.numVertices then
      if u == v then g  -- no self-loops
      else if (g.adj[u]'(g.h_size ▸ hu)).contains v then g  -- already exists
      else
        let hu' : u < g.adj.size := g.h_size ▸ hu
        let hv' : v < g.adj.size := g.h_size ▸ hv
        let adj1 := g.adj.set u (v :: g.adj[u]'hu') hu'
        have hv1 : v < adj1.size := by rw [Array.size_set]; exact hv'
        let adj2 := adj1.set v (u :: adj1[v]'hv1) hv1
        { numVertices := g.numVertices
          adj := adj2
          h_size := by rw [Array.size_set, Array.size_set]; exact g.h_size }
    else g
  else g

/-- The complete graph K_n: every pair of distinct vertices connected. -/
def completeGraph (n : Nat) : SimpleGraph where
  numVertices := n
  adj := Array.ofFn fun (i : Fin n) =>
    (List.range n).filter (· != i.val)
  h_size := by simp

/-- Star graph S_n: vertex 0 connected to all others. -/
def starGraph (n : Nat) : SimpleGraph where
  numVertices := n
  adj := Array.ofFn fun (i : Fin n) =>
    if i.val == 0 then (List.range n).filter (· != 0)
    else [0]
  h_size := by simp

/-- Path graph P_n: vertex i connected to i-1 and i+1. -/
def pathGraph (n : Nat) : SimpleGraph where
  numVertices := n
  adj := Array.ofFn fun (i : Fin n) =>
    let prev := if i.val > 0 then [i.val - 1] else []
    let next := if i.val + 1 < n then [i.val + 1] else []
    prev ++ next
  h_size := by simp

/-! ## Basic graph properties -/

theorem emptyGraph_numVertices (n : Nat) : (emptyGraph n).numVertices = n := rfl

theorem completeGraph_numVertices (n : Nat) : (completeGraph n).numVertices = n := rfl

theorem starGraph_numVertices (n : Nat) : (starGraph n).numVertices = n := rfl

theorem pathGraph_numVertices (n : Nat) : (pathGraph n).numVertices = n := rfl

/-! ## Max/Min degree -/

/-- Maximum degree over all vertices. Returns 0 for the empty graph. -/
def maxDegree (g : SimpleGraph) : Nat :=
  g.adj.foldl (fun acc nbrs => Nat.max acc nbrs.length) 0

/-- Minimum degree over all vertices. Returns 0 for the empty graph. -/
def minDegree (g : SimpleGraph) : Nat :=
  if g.numVertices == 0 then 0
  else g.adj.foldl (fun acc nbrs => Nat.min acc nbrs.length) g.adj[0]!.length

/-- Find vertex with minimum degree. Returns 0 for the empty graph. -/
def minDegreeVertex (g : SimpleGraph) : Nat :=
  if g.numVertices == 0 then 0
  else
    let init := (0, g.adj[0]!.length)
    let result := g.adj.foldl (init := (init, 1)) fun (best, idx) nbrs =>
      if nbrs.length < best.2 then ((idx, nbrs.length), idx + 1)
      else (best, idx + 1)
    result.1.1

/-! ## Induced subgraph -/

/-- Remove a vertex and all its edges. Vertices > v shift down by 1. -/
def removeVertex (g : SimpleGraph) (v : Nat) : SimpleGraph :=
  if v ≥ g.numVertices then g
  else
    let n := g.numVertices - 1
    let remap (x : Nat) : Nat := if x < v then x else x - 1
    let newAdj := Array.ofFn fun (i : Fin n) =>
      let oldI := if i.val < v then i.val else i.val + 1
      if h : oldI < g.numVertices then
        ((g.adj[oldI]'(g.h_size ▸ h)).filter (· != v)).map remap
      else []
    { numVertices := n
      adj := newAdj
      h_size := by simp [newAdj] }

/-! ## Clique operations -/

/-- Make all vertices in `verts` pairwise adjacent. -/
def makeClique (g : SimpleGraph) (verts : List Nat) : SimpleGraph :=
  verts.foldl (fun g1 u =>
    verts.foldl (fun g2 v =>
      if u < v then addEdge g2 u v else g2
    ) g1
  ) g

/-! ## Concrete tests (validated by native_decide) -/

theorem completeGraph_4_edges : numEdges (completeGraph 4) = 6 := by native_decide

theorem pathGraph_4_edges : numEdges (pathGraph 4) = 3 := by native_decide

theorem starGraph_4_edges : numEdges (starGraph 4) = 3 := by native_decide

end SuperHash.Graph
