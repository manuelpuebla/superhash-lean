import SuperHash.Pipeline.Integration
import SuperHash.Pipeline.Instances

/-!
# SuperHash.Pipeline.MasterTheorem — Master Soundness Theorem

Provides the crown-jewel result: `pipeline_soundness`, which bundles three properties:
1. **Semantic correctness**: every extracted design evaluates to the root value
2. **Pareto optimality**: no design in the output is dominated by another
3. **Termination**: the pipeline terminates (fuel-based, structurally guaranteed)

Plus a non-vacuity example demonstrating that all hypotheses are jointly satisfiable.
-/

namespace SuperHash

open UnionFind

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Master Soundness Theorem
-- ══════════════════════════════════════════════════════════════════

set_option maxHeartbeats 8000000 in
/-- **SuperHash Master Soundness Theorem.**
    Given a valid initial E-graph and sound rewrite rules, the pipeline produces
    a semantically correct, Pareto-optimal, bounded set of designs.

    Part 1 (semantic correctness): there exists a valuation v_sat such that
    every extracted design evaluates to the root's value in the saturated graph.

    Part 2 (Pareto optimality): no design in the output is dominated by another.

    Part 3 (output bound): the number of output designs is at most the number
    of weight vectors (since each weight vector produces at most one design). -/
theorem pipeline_soundness
    (rules : List (PatternSoundRule CryptoOp Nat))
    (g : EGraph CryptoOp)
    (fuel maxIter rebuildFuel : Nat)
    (weights : List Weights)
    (costFuel : Nat)
    (rootId : EClassId)
    (env : Nat → Nat) (v : EClassId → Nat)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g)
    (hshi : SemanticHashconsInv g env v)
    (hhcb : HashconsChildrenBounded g)
    (hbni : BestNodeInv g.classes) :
    let output := superhash_pipeline (rules.map (·.rule)) g fuel maxIter rebuildFuel
                                      weights costFuel rootId
    let g_sat := saturateF fuel maxIter rebuildFuel g (rules.map (·.rule))
    -- Part 1: Semantic correctness
    (∃ v_sat : EClassId → Nat,
      ∀ p ∈ output, EvalExpr.evalExpr p.1 env = v_sat (root g_sat.unionFind rootId)) ∧
    -- Part 2: Pareto optimality
    (∀ p1 ∈ output, ∀ p2 ∈ output, p1 ≠ p2 → ¬ dominates p1.2 p2.2) ∧
    -- Part 3: Output size bound
    output.length ≤ weights.length := by
  constructor
  · exact superhash_pipeline_correct rules g fuel maxIter rebuildFuel weights costFuel
      rootId env v hcv hpmi hshi hhcb hbni crypto_extractable_sound
  constructor
  · exact superhash_pipeline_no_dominated (rules.map (·.rule)) g fuel maxIter rebuildFuel
      weights costFuel rootId
  · simp only [superhash_pipeline]
    exact extractPareto_length_le _ _ _ _

/-- **Metrics correctness complement.**
    Every output pair (expr, metrics) has metrics = expr.metrics.
    Stated separately from `pipeline_soundness` to avoid heartbeat pressure. -/
theorem pipeline_metrics_correct
    (rules : List (RewriteRule CryptoOp))
    (g : EGraph CryptoOp)
    (fuel maxIter rebuildFuel : Nat)
    (weights : List Weights)
    (costFuel : Nat)
    (rootId : EClassId) :
    ∀ p ∈ superhash_pipeline rules g fuel maxIter rebuildFuel weights costFuel rootId,
      p.2 = p.1.metrics :=
  superhash_pipeline_metrics_correct rules g fuel maxIter rebuildFuel weights costFuel rootId

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Non-vacuity — all hypotheses are jointly satisfiable
-- ══════════════════════════════════════════════════════════════════

/-- PostMergeInvariant holds for the empty E-graph. -/
theorem empty_pmi : PostMergeInvariant (Op := CryptoOp) EGraph.empty where
  uf_wf := empty_wf
  children_bounded := fun _ _ h => by
    simp [EGraph.empty, Std.HashMap.get?_eq_getElem?] at h
  hashcons_entries_valid := fun _ _ h => by
    simp [EGraph.empty, Std.HashMap.get?_eq_getElem?] at h
  classes_entries_valid := fun _ h => by
    simp [EGraph.empty, Std.HashMap.contains_eq_isSome_getElem?] at h

/-- BestNodeInv holds for the empty E-graph (vacuously). -/
theorem empty_bni : BestNodeInv (Op := CryptoOp) (EGraph.empty).classes :=
  fun _ _ _ h => by simp [EGraph.empty, Std.HashMap.get?_eq_getElem?] at h

-- Non-vacuity example is in Tests/NonVacuity/Pipeline.lean
-- (moved there to keep this file's compile time reasonable)

-- Smoke test
#check @pipeline_soundness

end SuperHash
