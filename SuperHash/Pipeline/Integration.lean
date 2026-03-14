import SuperHash.CryptoOp
import SuperHash.Pareto.Soundness

/-!
# SuperHash.Pipeline.Integration — Full pipeline composition

Provides:
- `superhash_pipeline`: compose saturateF → computeCosts → extractPareto
- `superhash_pipeline_correct`: semantic correctness of the full pipeline
- `superhash_pipeline_no_dominated`: Pareto property of the pipeline output

This is the top-level pipeline that takes an initial E-graph with crypto designs,
saturates with sound rewrite rules, and extracts the Pareto-optimal designs.
-/

namespace SuperHash

open UnionFind

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Full pipeline
-- ══════════════════════════════════════════════════════════════════

/-- **SuperHash full pipeline.**
    Composes: saturateF → extractPareto (which internally uses computeCostsF + extractAuto).

    Parameters:
    - `rules`: sound rewrite rules for saturation
    - `g`: initial E-graph with crypto design
    - `fuel`: fuel for ematch/instantiate per saturation step
    - `maxIter`: maximum saturation iterations
    - `rebuildFuel`: fuel for rebuild per saturation step
    - `weights`: weight vectors for multi-objective extraction
    - `costFuel`: fuel for cost computation convergence

    Returns: list of (CryptoExpr, SecurityMetrics) pairs — the Pareto front. -/
def superhash_pipeline
    (rules : List (RewriteRule CryptoOp))
    (g : EGraph CryptoOp)
    (fuel maxIter rebuildFuel : Nat)
    (weights : List Weights)
    (costFuel : Nat)
    (rootId : EClassId) : List (CryptoExpr × SecurityMetrics) :=
  let g_sat := saturateF fuel maxIter rebuildFuel g rules
  extractPareto g_sat weights costFuel rootId

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Pipeline soundness bridge
-- ══════════════════════════════════════════════════════════════════

set_option maxHeartbeats 800000 in
/-- **Pipeline preserves semantic correctness.**
    Every design in the pipeline output evaluates to the root value of the
    saturated graph, using a consistent valuation that exists by
    `saturateF_preserves_consistent_internal`. -/
theorem superhash_pipeline_correct
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
    (hbni : BestNodeInv g.classes)
    (hsound : ExtractableSound CryptoOp CryptoExpr Nat) :
    ∃ v_sat : EClassId → Nat,
      ∀ p ∈ superhash_pipeline (rules.map (·.rule)) g fuel maxIter rebuildFuel
                                weights costFuel rootId,
        EvalExpr.evalExpr p.1 env =
          v_sat (root (saturateF fuel maxIter rebuildFuel g (rules.map (·.rule))).unionFind rootId) := by
  -- Step 1: saturateF preserves consistent valuation
  obtain ⟨v_sat, hcv_sat⟩ := saturateF_preserves_consistent_internal fuel maxIter
    rebuildFuel g rules env v hcv hpmi hshi hhcb sameShapeSemantics_holds
    (InstantiateEvalSound_holds env)
    (fun g' rule hrule hpmi' classId hclass σ hmem pv id hσ =>
      ematchF_substitution_bounded g' hpmi' fuel rule.rule.lhs classId ∅ hclass
        (fun pv' id' h => absurd h (by rw [Std.HashMap.get?_eq_getElem?]; simp))
        σ hmem pv id hσ)
  -- Step 2: saturateF preserves WF and BNI
  have hwf_sat := saturateF_preserves_wf fuel maxIter rebuildFuel g rules env v
    hcv hpmi hshi hhcb
  have hbni_sat := saturateF_preserves_bni fuel maxIter rebuildFuel g
    (rules.map (·.rule)) hbni
  -- Step 3: compose with extractPareto correctness
  refine ⟨v_sat, ?_⟩
  simp only [superhash_pipeline]
  exact extractPareto_all_correct _ weights costFuel rootId env v_sat
    hcv_sat hwf_sat hbni_sat hsound

/-- **Pipeline Pareto property.**
    No design in the pipeline output dominates another. -/
theorem superhash_pipeline_no_dominated
    (rules : List (RewriteRule CryptoOp))
    (g : EGraph CryptoOp)
    (fuel maxIter rebuildFuel : Nat)
    (weights : List Weights)
    (costFuel : Nat)
    (rootId : EClassId) :
    ∀ p1 ∈ superhash_pipeline rules g fuel maxIter rebuildFuel weights costFuel rootId,
    ∀ p2 ∈ superhash_pipeline rules g fuel maxIter rebuildFuel weights costFuel rootId,
      p1 ≠ p2 → ¬ dominates p1.2 p2.2 := by
  simp only [superhash_pipeline]
  exact extractPareto_no_dominated _ _ _ _

/-- **Pipeline output size bound.**
    The number of designs is at most the number of weight vectors. -/
theorem superhash_pipeline_length_le
    (rules : List (RewriteRule CryptoOp))
    (g : EGraph CryptoOp)
    (fuel maxIter rebuildFuel : Nat)
    (weights : List Weights)
    (costFuel : Nat)
    (rootId : EClassId) :
    (superhash_pipeline rules g fuel maxIter rebuildFuel weights costFuel rootId).length
    ≤ weights.length := by
  simp only [superhash_pipeline]
  exact extractPareto_length_le _ _ _ _

/-- **Pipeline metrics bridge.**
    Every design in the output has p.2 = p.1.metrics. -/
theorem superhash_pipeline_metrics_correct
    (rules : List (RewriteRule CryptoOp))
    (g : EGraph CryptoOp)
    (fuel maxIter rebuildFuel : Nat)
    (weights : List Weights)
    (costFuel : Nat)
    (rootId : EClassId) :
    ∀ p ∈ superhash_pipeline rules g fuel maxIter rebuildFuel weights costFuel rootId,
      p.2 = p.1.metrics := by
  simp only [superhash_pipeline]
  exact extractPareto_metrics_correct _ _ _ _

-- Smoke test
#check @superhash_pipeline
#check @superhash_pipeline_correct
#check @superhash_pipeline_no_dominated
#check @superhash_pipeline_length_le
#check @superhash_pipeline_metrics_correct

end SuperHash
