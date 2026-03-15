import SuperHash.Attack.AttackInstances
import SuperHash.Pipeline.Soundness

/-!
# SuperHash.Attack.AttackPipeline — Master Soundness for Red Team

Composes the attack-side pipeline infrastructure into a master theorem:
`attack_pipeline_soundness` — a 3-part result for the Red Team:
  Part 1: Semantic correctness (AttackSemantics)
  Part 2: Extraction soundness (extractF produces correct AttackExpr)
  Part 3: Saturation preserves all invariants

## Architecture
The pipeline infrastructure is PARAMETRIC over `[NodeSemantics Op Val]`.
Phase 1 provided `NodeSemantics AttackOp AttackSemantics` (AttackNodeSemantics.lean).
Phase 2 provided `Extractable AttackOp AttackExpr` and
`ExtractableSound AttackOp AttackExpr AttackSemantics` (AttackInstances.lean).

This file composes these into the master soundness statement.
-/

set_option linter.unusedSimpArgs false

namespace SuperHash

open UnionFind

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Saturation preserves AttackSemantics consistency
-- ══════════════════════════════════════════════════════════════════

/-- Saturation preserves ConsistentValuation for AttackSemantics.
    Direct application of the parametric `saturateF_preserves_consistent_internal`
    at `Op := AttackOp`, `Val := AttackSemantics`. -/
theorem attack_saturation_consistent
    (rules : List (PatternSoundRule AttackOp AttackSemantics))
    (g : EGraph AttackOp)
    (fuel maxIter rebuildFuel : Nat)
    (env : Nat → AttackSemantics) (v : EClassId → AttackSemantics)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g)
    (hshi : SemanticHashconsInv g env v)
    (hhcb : HashconsChildrenBounded g) :
    ∃ v_sat : EClassId → AttackSemantics,
      ConsistentValuation (saturateF fuel maxIter rebuildFuel g (rules.map (·.rule))) env v_sat := by
  obtain ⟨v_sat, hcv_sat⟩ := saturateF_preserves_consistent_internal fuel maxIter
    rebuildFuel g rules env v hcv hpmi hshi hhcb sameShapeSemantics_holds
    (InstantiateEvalSound_holds env)
    (fun g' rule hrule hpmi' classId hclass σ hmem pv id hσ =>
      ematchF_substitution_bounded g' hpmi' fuel rule.rule.lhs classId ∅ hclass
        (fun pv' id' h => absurd h (by rw [Std.HashMap.get?_eq_getElem?]; simp))
        σ hmem pv id hσ)
  exact ⟨v_sat, hcv_sat⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Extraction correctness for AttackSemantics
-- ══════════════════════════════════════════════════════════════════

/-- Extraction produces semantically correct AttackExpr from e-graph.
    Direct application of parametric `computeCostsF_extractF_correct`
    at AttackOp/AttackExpr/AttackSemantics. -/
theorem attack_extractF_correct (g : EGraph AttackOp)
    (costFn : ENode AttackOp → Nat) (costFuel : Nat)
    (env : Nat → AttackSemantics) (v : EClassId → AttackSemantics)
    (hcv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (rootId : EClassId) (expr : AttackExpr)
    (hext : extractF (computeCostsF g costFn costFuel) rootId costFuel = some expr) :
    EvalExpr.evalExpr expr env = v (root g.unionFind rootId) :=
  computeCostsF_extractF_correct g costFn costFuel env v
    hcv hwf hbni attack_extractable_sound _ rootId expr hext

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Master Soundness Theorem for Red Team
-- ══════════════════════════════════════════════════════════════════

set_option maxHeartbeats 800000 in
/-- **Attack Pipeline Master Soundness Theorem.**
    Given a valid initial E-graph and AttackSemantics-sound rewrite rules,
    saturation produces a semantically correct e-graph from which any
    correctly extracted AttackExpr evaluates to the root's attack metrics.

    Part 1 (saturation correctness): there exists v_sat such that
    the saturated graph has consistent valuation under AttackSemantics.

    Part 2 (WellFormed preservation): the saturated graph is well-formed.

    Part 3 (BestNodeInv preservation): BestNodeInv is preserved. -/
theorem attack_pipeline_soundness
    (rules : List (PatternSoundRule AttackOp AttackSemantics))
    (g : EGraph AttackOp)
    (fuel maxIter rebuildFuel : Nat)
    (env : Nat → AttackSemantics) (v : EClassId → AttackSemantics)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g)
    (hshi : SemanticHashconsInv g env v)
    (hhcb : HashconsChildrenBounded g)
    (hbni : BestNodeInv g.classes) :
    let g_sat := saturateF fuel maxIter rebuildFuel g (rules.map (·.rule))
    -- Part 1: Semantic consistency preserved in AttackSemantics domain
    (∃ v_sat : EClassId → AttackSemantics,
      ConsistentValuation g_sat env v_sat) ∧
    -- Part 2: WellFormed preservation
    WellFormed g_sat.unionFind ∧
    -- Part 3: BestNodeInv preservation
    BestNodeInv g_sat.classes := by
  constructor
  · exact attack_saturation_consistent rules g fuel maxIter rebuildFuel env v
      hcv hpmi hshi hhcb
  constructor
  · exact saturateF_preserves_wf fuel maxIter rebuildFuel g rules env v
      hcv hpmi hshi hhcb
  · exact saturateF_preserves_bni fuel maxIter rebuildFuel g
      (rules.map (·.rule)) hbni

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Non-vacuity — all hypotheses are jointly satisfiable
-- ══════════════════════════════════════════════════════════════════

/-- PostMergeInvariant holds for the empty E-graph (AttackOp version). -/
theorem empty_pmi_attack : PostMergeInvariant (Op := AttackOp) EGraph.empty where
  uf_wf := empty_wf
  children_bounded := fun _ _ h => by
    simp [EGraph.empty, Std.HashMap.get?_eq_getElem?] at h
  hashcons_entries_valid := fun _ _ h => by
    simp [EGraph.empty, Std.HashMap.get?_eq_getElem?] at h
  classes_entries_valid := fun _ h => by
    simp [EGraph.empty, Std.HashMap.contains_eq_isSome_getElem?] at h

/-- BestNodeInv holds for the empty E-graph (AttackOp version, vacuously). -/
theorem empty_bni_attack : BestNodeInv (Op := AttackOp) (EGraph.empty).classes :=
  fun _ _ _ h => by simp [EGraph.empty, Std.HashMap.get?_eq_getElem?] at h

set_option linter.unusedVariables false in
/-- Non-vacuity: attack_pipeline_soundness hypotheses are jointly satisfiable.
    Uses the empty E-graph (trivially consistent), default environment. -/
example : ∃ (rules : List (PatternSoundRule AttackOp AttackSemantics))
    (g : EGraph AttackOp)
    (env : Nat → AttackSemantics)
    (v : EClassId → AttackSemantics),
    ConsistentValuation g env v ∧
    PostMergeInvariant g ∧
    SemanticHashconsInv g env v ∧
    HashconsChildrenBounded g ∧
    BestNodeInv g.classes := by
  refine ⟨[], EGraph.empty, fun _ => default, fun _ => default,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact empty_consistent _
  · exact empty_pmi_attack
  · intro _ _ h; simp [EGraph.empty, Std.HashMap.get?_eq_getElem?] at h
  · intro _ _ h; simp [EGraph.empty, Std.HashMap.get?_eq_getElem?] at h
  · exact empty_bni_attack

-- Smoke tests
#check @attack_pipeline_soundness
#check @attack_saturation_consistent
#check @attack_extractF_correct

end SuperHash
