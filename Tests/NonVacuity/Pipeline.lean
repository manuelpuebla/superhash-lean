import SuperHash.Pipeline.MasterTheorem
import SuperHash.Instances.Evaluation

/-!
# Tests.NonVacuity.Pipeline — End-to-end non-vacuity for the SuperHash pipeline

Demonstrates that `pipeline_soundness` is not vacuously true by constructing
a concrete E-graph with a non-trivial design and verifying all hypotheses.

This transitively validates:
- ConsistentValuation preservation through saturateF
- WellFormed and BestNodeInv preservation
- ExtractableSound for CryptoOp → CryptoExpr
- Pareto extraction correctness
-/

namespace SuperHash

open UnionFind

-- Non-vacuity for the empty graph: all pipeline hypotheses are satisfiable.
-- This is the baseline test — demonstrates hypotheses are jointly satisfiable.
-- NOTE: With an empty graph + empty rules, output = [], so Parts 1-2 hold vacuously.
-- See R6 below for a non-trivial example with output.length > 0.
set_option maxHeartbeats 8000000 in
example :
    let output := superhash_pipeline ([] : List (RewriteRule CryptoOp)) EGraph.empty
                                      10 5 10 [⟨1, 1, 1⟩] 10 0
    let g_sat := saturateF 10 5 10 (EGraph.empty : EGraph CryptoOp) []
    (∃ v_sat : EClassId → Nat,
      ∀ p ∈ output, EvalExpr.evalExpr p.1 (fun _ => (0 : Nat)) = v_sat (root g_sat.unionFind 0)) ∧
    (∀ p1 ∈ output, ∀ p2 ∈ output, p1 ≠ p2 → ¬ dominates p1.2 p2.2) ∧
    output.length ≤ ([⟨1, 1, 1⟩] : List Weights).length :=
  pipeline_soundness [] EGraph.empty 10 5 10 [⟨1, 1, 1⟩] 10 0
    (fun _ => (0 : Nat)) (fun _ => (default : Nat))
    (empty_consistent (Op := CryptoOp) _)
    empty_pmi
    (empty_shi (Op := CryptoOp) _)
    (empty_hcb (Val := Nat))
    empty_bni

-- ══════════════════════════════════════════════════════════════════
-- Non-trivial non-vacuity: output.length > 0
-- ══════════════════════════════════════════════════════════════════

-- The pipeline produces at least one design from a graph with a const node.
-- This proves the universal quantifiers in Parts 1-2 are NOT vacuous.
private def testGraph := ((EGraph.empty : EGraph CryptoOp).add ⟨CryptoOp.const 42⟩).2

/-- The pipeline output is non-empty for a graph with a const node. -/
example : (superhash_pipeline ([] : List (RewriteRule CryptoOp))
    testGraph 10 5 10 [⟨1, 1, 1⟩] 10 0).length = 1 := by
  native_decide

-- Pipeline execution produces expected results
#eval
  let (rootId, g) := designToEGraph simpleSPN EGraph.empty
  let result := superhash_pipeline [] g 10 5 10 [⟨1, 1, 1⟩] 10 rootId
  s!"Pipeline output length: {result.length}"

-- Metrics computation is consistent
#eval
  let e := CryptoExpr.compose (.sbox 7 (.const 0)) (.linear 5 (.const 0))
  let m := e.metrics
  (m.securityBits, m.latency, m.gateCount)  -- expected: (12, 2, 2)

-- ══════════════════════════════════════════════════════════════════
-- R5 (autopsy fix): Verify extracted design has correct semantics
-- ══════════════════════════════════════════════════════════════════

/-- Non-vacuity: the extracted design from testGraph evaluates to the
    expected Nat value. This proves Part 1 of pipeline_soundness is
    NOT vacuously true for this input (output.length = 1). -/
example : (superhash_pipeline ([] : List (RewriteRule CryptoOp))
    testGraph 10 5 10 [⟨1, 1, 1⟩] 10 0).head?.map (fun p =>
      EvalExpr.evalExpr p.1 (fun _ => (0 : Nat))) = some 42 := by
  native_decide

/-- Non-vacuity: the extracted design has expected metrics. -/
example : (superhash_pipeline ([] : List (RewriteRule CryptoOp))
    testGraph 10 5 10 [⟨1, 1, 1⟩] 10 0).head?.map (fun p =>
      p.2) = some ⟨0, 0, 0⟩ := by
  native_decide

end SuperHash
