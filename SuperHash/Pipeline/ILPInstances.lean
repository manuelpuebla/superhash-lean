/-
  SuperHash — ILP Instances for CryptoOp
  Phase 3: Instantiate ILP extraction for the cryptographic domain

  Provides:
  - `cryptoILPCostFn`: cost function for ILP encoding (delegates to NodeOps.localCost)
  - `encodeCryptoEGraph`: convenience wrapper for encoding CryptoOp e-graphs
  - `extractCryptoILP`: convenience wrapper for ILP extraction
  - `ilp_extraction_soundness_crypto`: bridge theorem for CryptoOp pipeline
  - Non-vacuity example with concrete ILPSolution
-/
import SuperHash.Pipeline.ILPSpec
import SuperHash.Pipeline.Instances
import SuperHash.Pipeline.ExtractionStrategy

namespace SuperHash

open ILP UnionFind

-- ══════════════════════════════════════════════════════════════════
-- CryptoOp ILP Cost Function
-- ══════════════════════════════════════════════════════════════════

/-- Cost function for ILP encoding: uses `NodeOps.localCost` (identical to `cryptoCostFn`). -/
def cryptoILPCostFn (node : ENode CryptoOp) : Nat :=
  NodeOps.localCost node.op

-- ══════════════════════════════════════════════════════════════════
-- Convenience Wrappers
-- ══════════════════════════════════════════════════════════════════

/-- Encode a CryptoOp e-graph as an ILP problem. -/
def encodeCryptoEGraph (g : EGraph CryptoOp) (rootId : EClassId) : ILPProblem :=
  encodeEGraph g rootId cryptoILPCostFn

/-- Extract a CryptoExpr from a CryptoOp e-graph using an ILP solution. -/
def extractCryptoILP (g : EGraph CryptoOp) (sol : ILPSolution) (rootId : EClassId)
    (fuel : Nat) : Option CryptoExpr :=
  extractILP g sol rootId fuel

/-- Convenience: auto-fueled ILP extraction for CryptoOp. -/
def extractCryptoILPAuto (g : EGraph CryptoOp) (sol : ILPSolution)
    (rootId : EClassId) : Option CryptoExpr :=
  extractILPAuto g sol rootId

-- ══════════════════════════════════════════════════════════════════
-- Bridge: ILP extraction soundness for CryptoOp
-- ══════════════════════════════════════════════════════════════════

/-- ILP extraction for CryptoOp is semantically correct:
    if extractILP succeeds on a valid ILP solution over a consistent e-graph,
    the extracted CryptoExpr evaluates to the root class's value. -/
theorem ilp_extraction_soundness_crypto
    (g : EGraph CryptoOp) (rootId : EClassId)
    (sol : ILPSolution) (env : Nat → Nat) (v : EClassId → Nat)
    (hcv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (hvalid : ValidSolution g rootId sol)
    (fuel : Nat) (expr : CryptoExpr)
    (hext : extractILP g sol rootId fuel = some expr) :
    CryptoExpr.eval expr env = v (root g.unionFind rootId) :=
  ilp_extraction_soundness g rootId sol env v hcv hwf hvalid
    crypto_extractable_sound fuel expr hext

/-- Unified extraction correctness for CryptoOp: works for both greedy and ILP. -/
theorem extract_correct_crypto
    (g : EGraph CryptoOp) (env : Nat → Nat) (v : EClassId → Nat)
    (hcv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (rootId : EClassId) (strategy : ExtractionStrategy CryptoOp)
    (hvalid : StrategyValid g rootId strategy)
    (expr : CryptoExpr)
    (hext : extract g rootId strategy = some expr) :
    CryptoExpr.eval expr env = v (root g.unionFind rootId) :=
  extract_correct g env v hcv hwf crypto_extractable_sound rootId strategy hvalid expr hext

-- ══════════════════════════════════════════════════════════════════
-- Non-vacuity: concrete ILP solution on a trivial e-graph
-- ══════════════════════════════════════════════════════════════════

/-- Construct a trivial e-graph with a single `const 42` node for non-vacuity testing.
    Returns (rootId, graph). -/
private def trivialEGraph : EClassId × EGraph CryptoOp :=
  let g0 : EGraph CryptoOp := EGraph.empty
  g0.add (ENode.mk (.const 42))

/-- ILP solution that selects the single node in class 0. -/
private def trivialILPSolution : ILPSolution where
  selectedNodes := Std.HashMap.ofList [(0, 0)]
  activatedClasses := Std.HashMap.ofList [(0, true)]
  levels := Std.HashMap.ofList [(0, 0)]
  objectiveValue := 0

/-- Non-vacuity: checkSolution passes for the trivial e-graph + solution. -/
example : checkSolution trivialEGraph.2 trivialEGraph.1 trivialILPSolution = true := by
  native_decide

/-- Non-vacuity: extractILP succeeds on the trivial e-graph. -/
example : (extractILP (Expr := CryptoExpr) trivialEGraph.2 trivialILPSolution
    trivialEGraph.1 1).isSome = true := by
  native_decide

-- ══════════════════════════════════════════════════════════════════
-- Smoke Tests
-- ══════════════════════════════════════════════════════════════════

#eval do
  let (rid, g) := trivialEGraph
  let prob := encodeCryptoEGraph g rid
  return (prob.numClasses, decide (prob.numConstraints > 0))  -- (1, true)

#eval do
  let (rid, g) := trivialEGraph
  let result := extractCryptoILP g trivialILPSolution rid 2
  return result.isSome  -- true

end SuperHash
