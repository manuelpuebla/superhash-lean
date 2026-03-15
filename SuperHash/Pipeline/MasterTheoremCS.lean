import SuperHash.Pipeline.Integration
import SuperHash.Pipeline.Instances
import SuperHash.Pipeline.MasterTheorem
import SuperHash.Rules.CryptoRulesCS

/-!
# SuperHash.Pipeline.MasterTheoremCS — Master Soundness over CryptoSemantics

The crown-jewel result for real cryptographic semantics:
`pipeline_soundness_crypto`, which states that the SuperHash pipeline
produces semantically correct designs when interpreted in the
CryptoSemantics domain (7-field metric struct: algebraicDegree,
differentialUniformity, linearBias, branchNumber, activeMinSboxes,
latency, gateCount).

## Architecture
The pipeline infrastructure (saturateF, extractF, computeCostsF) is
PARAMETRIC over `[NodeSemantics Op Val]`. The Pareto extraction layer
(extractPareto) is specialized to CryptoOp but its correctness proofs
chain through the parametric `computeCostsF_extractF_correct`.

This file:
1. Proves a CryptoSemantics version of extractPareto correctness
2. Composes into `superhash_pipeline_correct_crypto`
3. Bundles into `pipeline_soundness_crypto` (3-part master theorem)
4. Provides a non-vacuity example

## Key insight
The SAME `superhash_pipeline` function is used (it is Val-agnostic at
the computation level). The soundness proof simply instantiates the
parametric pipeline theorems at `Val := CryptoSemantics`, using:
- `NodeSemantics CryptoOp CryptoSemantics` (from CryptoNodeSemantics.lean)
- `EvalExpr CryptoExpr CryptoSemantics` (from Instances.lean)
- `ExtractableSound CryptoOp CryptoExpr CryptoSemantics` (from Instances.lean)
-/

set_option linter.unusedSimpArgs false

namespace SuperHash

open UnionFind

-- ══════════════════════════════════════════════════════════════════
-- Section 1: CryptoSemantics extraction correctness bridge
-- ══════════════════════════════════════════════════════════════════

/-- Each design extracted by extractWeighted evaluates to the root value
    in the CryptoSemantics domain. Bridges through the parametric
    computeCostsF_extractF_correct. -/
theorem extractWeighted_correct_cs (g : EGraph CryptoOp) (w : Weights) (costFuel : Nat)
    (env : Nat → CryptoSemantics) (v : EClassId → CryptoSemantics)
    (hcv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (hsound : ExtractableSound CryptoOp CryptoExpr CryptoSemantics)
    (rootId : EClassId) (expr : CryptoExpr)
    (hext : extractWeighted g w costFuel rootId = some expr) :
    EvalExpr.evalExpr expr env = v (root g.unionFind rootId) := by
  unfold extractWeighted at hext
  exact computeCostsF_extractF_correct g (weightedCostFn w) costFuel env v
    hcv hwf hbni hsound _ rootId expr hext

/-- All designs from extractAll evaluate to the root value in CryptoSemantics. -/
theorem extractAll_correct_cs (g : EGraph CryptoOp) (weights : List Weights) (costFuel : Nat)
    (env : Nat → CryptoSemantics) (v : EClassId → CryptoSemantics)
    (hcv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (hsound : ExtractableSound CryptoOp CryptoExpr CryptoSemantics)
    (rootId : EClassId) :
    ∀ p ∈ extractAll g weights costFuel rootId,
      EvalExpr.evalExpr p.1 env = v (root g.unionFind rootId) := by
  intro ⟨expr, m⟩ hmem
  simp only [extractAll, List.mem_map, List.mem_filterMap] at hmem
  obtain ⟨e, ⟨w, _hw, hew⟩, heq⟩ := hmem
  simp at heq
  obtain ⟨rfl, _⟩ := heq
  exact extractWeighted_correct_cs g w costFuel env v hcv hwf hbni hsound rootId e hew

/-- Every design in the Pareto extraction evaluates to the root value
    in CryptoSemantics. -/
theorem extractPareto_all_correct_cs (g : EGraph CryptoOp) (weights : List Weights)
    (costFuel : Nat) (rootId : EClassId)
    (env : Nat → CryptoSemantics) (v : EClassId → CryptoSemantics)
    (hcv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (hsound : ExtractableSound CryptoOp CryptoExpr CryptoSemantics) :
    ∀ p ∈ extractPareto g weights costFuel rootId,
      EvalExpr.evalExpr p.1 env = v (root g.unionFind rootId) := by
  intro p hp
  simp only [extractPareto] at hp
  rw [List.mem_filter] at hp
  obtain ⟨hp_dedup, _⟩ := hp
  have hp_all := dedup_subset (extractAll g weights costFuel rootId) p hp_dedup
  exact extractAll_correct_cs g weights costFuel env v hcv hwf hbni hsound rootId p hp_all

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Pipeline correctness over CryptoSemantics
-- ══════════════════════════════════════════════════════════════════

set_option maxHeartbeats 800000 in
/-- **Pipeline preserves semantic correctness in CryptoSemantics domain.**
    Every design in the pipeline output evaluates to the root value of the
    saturated graph under CryptoSemantics (real cryptographic metrics). -/
theorem superhash_pipeline_correct_crypto
    (rules : List (PatternSoundRule CryptoOp CryptoSemantics))
    (g : EGraph CryptoOp)
    (fuel maxIter rebuildFuel : Nat)
    (weights : List Weights)
    (costFuel : Nat)
    (rootId : EClassId)
    (env : Nat → CryptoSemantics) (v : EClassId → CryptoSemantics)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g)
    (hshi : SemanticHashconsInv g env v)
    (hhcb : HashconsChildrenBounded g)
    (hbni : BestNodeInv g.classes)
    (hsound : ExtractableSound CryptoOp CryptoExpr CryptoSemantics) :
    ∃ v_sat : EClassId → CryptoSemantics,
      ∀ p ∈ superhash_pipeline (rules.map (·.rule)) g fuel maxIter rebuildFuel
                                weights costFuel rootId,
        EvalExpr.evalExpr p.1 env =
          v_sat (root (saturateF fuel maxIter rebuildFuel g (rules.map (·.rule))).unionFind rootId) := by
  -- Step 1: saturateF preserves consistent valuation (parametric at CryptoSemantics)
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
  -- Step 3: compose with extractPareto correctness (CryptoSemantics version)
  refine ⟨v_sat, ?_⟩
  simp only [superhash_pipeline]
  exact extractPareto_all_correct_cs _ weights costFuel rootId env v_sat
    hcv_sat hwf_sat hbni_sat hsound

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Master Soundness Theorem over CryptoSemantics
-- ══════════════════════════════════════════════════════════════════

set_option maxHeartbeats 8000000 in
/-- **SuperHash Master Soundness Theorem over CryptoSemantics.**
    Given a valid initial E-graph and CryptoSemantics-sound rewrite rules,
    the pipeline produces a semantically correct, Pareto-optimal, bounded
    set of designs — with correctness in the REAL cryptographic metric domain.

    Part 1 (semantic correctness): there exists a CryptoSemantics valuation
    v_sat such that every extracted design evaluates to the root's value.

    Part 2 (Pareto optimality): no design in the output is dominated by another.

    Part 3 (output bound): the number of output designs ≤ weight vectors. -/
theorem pipeline_soundness_crypto
    (rules : List (PatternSoundRule CryptoOp CryptoSemantics))
    (g : EGraph CryptoOp)
    (fuel maxIter rebuildFuel : Nat)
    (weights : List Weights)
    (costFuel : Nat)
    (rootId : EClassId)
    (env : Nat → CryptoSemantics) (v : EClassId → CryptoSemantics)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g)
    (hshi : SemanticHashconsInv g env v)
    (hhcb : HashconsChildrenBounded g)
    (hbni : BestNodeInv g.classes) :
    let output := superhash_pipeline (rules.map (·.rule)) g fuel maxIter rebuildFuel
                                      weights costFuel rootId
    let g_sat := saturateF fuel maxIter rebuildFuel g (rules.map (·.rule))
    -- Part 1: Semantic correctness in CryptoSemantics domain
    (∃ v_sat : EClassId → CryptoSemantics,
      ∀ p ∈ output, EvalExpr.evalExpr p.1 env = v_sat (root g_sat.unionFind rootId)) ∧
    -- Part 2: Pareto optimality
    (∀ p1 ∈ output, ∀ p2 ∈ output, p1 ≠ p2 → ¬ dominates p1.2 p2.2) ∧
    -- Part 3: Output size bound
    output.length ≤ weights.length := by
  constructor
  · exact superhash_pipeline_correct_crypto rules g fuel maxIter rebuildFuel weights costFuel
      rootId env v hcv hpmi hshi hhcb hbni crypto_extractable_sound_cs
  constructor
  · exact superhash_pipeline_no_dominated (rules.map (·.rule)) g fuel maxIter rebuildFuel
      weights costFuel rootId
  · simp only [superhash_pipeline]
    exact extractPareto_length_le _ _ _ _

/-- **Metrics correctness complement (CryptoSemantics).**
    Every output pair (expr, metrics) has metrics = expr.metrics.
    Independent of Val — same as the Nat version. -/
theorem pipeline_metrics_correct_crypto
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
-- Section 4: Non-vacuity — all hypotheses are jointly satisfiable
-- ══════════════════════════════════════════════════════════════════

set_option linter.unusedVariables false in
/-- Non-vacuity: pipeline_soundness_crypto hypotheses are jointly satisfiable.
    Uses the empty E-graph (trivially consistent), default environment,
    and cryptoPatternRulesCS (3 CryptoSemantics-sound rules). -/
example : ∃ (rules : List (PatternSoundRule CryptoOp CryptoSemantics))
    (g : EGraph CryptoOp)
    (env : Nat → CryptoSemantics)
    (v : EClassId → CryptoSemantics),
    ConsistentValuation g env v ∧
    PostMergeInvariant g ∧
    SemanticHashconsInv g env v ∧
    HashconsChildrenBounded g ∧
    BestNodeInv g.classes := by
  refine ⟨cryptoPatternRulesCS, EGraph.empty, fun _ => default, fun _ => default,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact empty_consistent _
  · exact empty_pmi
  · intro _ _ h; simp [EGraph.empty, Std.HashMap.get?_eq_getElem?] at h
  · intro _ _ h; simp [EGraph.empty, Std.HashMap.get?_eq_getElem?] at h
  · exact empty_bni

-- Smoke tests
#check @pipeline_soundness_crypto
#check @superhash_pipeline_correct_crypto
#check @extractPareto_all_correct_cs

end SuperHash
