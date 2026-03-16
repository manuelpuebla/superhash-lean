import SuperHash

/-!
# Tests.NonVacuity.SpecWitnesses — Non-vacuity for key Spec theorems (v4.5.8)

Demonstrates that hypotheses of key specification theorems are jointly satisfiable
using `EGraph.empty` and default environments/valuations.

Each `example` compiles without `sorry` and witnesses concrete satisfiability.
-/

open SuperHash
open UnionFind

-- ============================================================
-- Section 1: EGraph CoreSpec — structural invariants
-- ============================================================

/-- EGraphWF holds for the empty E-graph. -/
example : @EGraphWF CryptoOp _ _ _ EGraph.empty :=
  egraph_empty_wf

/-- PostMergeInvariant holds for the empty E-graph (CryptoOp). -/
example : PostMergeInvariant (Op := CryptoOp) EGraph.empty :=
  empty_pmi

/-- AddExprInv is derivable from EGraphWF for the empty E-graph. -/
example : AddExprInv (Op := CryptoOp) EGraph.empty :=
  EGraphWF.toAddExprInv egraph_empty_wf

-- ============================================================
-- Section 2: Consistency — valuation invariants on empty graph
-- ============================================================

/-- ConsistentValuation holds for empty graph with default valuation (Nat). -/
example : ConsistentValuation (Op := CryptoOp) (Val := Nat)
    EGraph.empty (fun _ => 0) (fun _ => default) :=
  empty_consistent _

/-- SemanticHashconsInv holds for empty graph with default valuation (Nat). -/
example : SemanticHashconsInv (Op := CryptoOp) (Val := Nat)
    EGraph.empty (fun _ => 0) (fun _ => default) :=
  empty_shi (Op := CryptoOp) _

/-- HashconsChildrenBounded holds for empty graph. -/
example : HashconsChildrenBounded (Op := CryptoOp) EGraph.empty :=
  empty_hcb (Val := Nat)

/-- BestNodeInv holds for empty graph (vacuously). -/
example : BestNodeInv (EGraph.empty (Op := CryptoOp)).classes :=
  bestNodeInv_empty

-- ============================================================
-- Section 3: Pipeline Master Theorem — all hypotheses jointly satisfiable
-- ============================================================

-- pipeline_soundness hypotheses are jointly satisfiable on the empty graph.
-- This transitively validates:
-- - ConsistentValuation preservation through saturateF
-- - WellFormed and BestNodeInv preservation
-- - ExtractableSound for CryptoOp / CryptoExpr
-- - Pareto extraction correctness
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
