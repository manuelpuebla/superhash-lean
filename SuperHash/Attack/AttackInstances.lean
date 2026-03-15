import SuperHash.Attack.AttackExpr

/-!
# SuperHash.Attack.AttackInstances — ExtractableSound for attack pipeline

Proves `attack_extractable_sound : ExtractableSound AttackOp AttackExpr AttackSemantics`.
This is the KEY bridge theorem that connects:
- extracted AttackExpr evaluation (via AttackExpr.eval)
- e-graph NodeSemantics evaluation (via evalAttackOpAS)

14-case proof (one per AttackOp constructor), each by simp + rewrite.
Follows the same pattern as `crypto_extractable_sound_cs` in Pipeline/Instances.lean.
-/

set_option linter.unusedSimpArgs false

namespace SuperHash

-- ============================================================
-- ExtractableSound for AttackOp/AttackExpr/AttackSemantics
-- ============================================================

/-- ExtractableSound for AttackOp/AttackExpr/AttackSemantics.
    Bridges extracted AttackExpr evaluation (via eval) to
    e-graph NodeSemantics evaluation (via evalAttackOpAS).
    14-case proof: one per AttackOp constructor. -/
theorem attack_extractable_sound : ExtractableSound AttackOp AttackExpr AttackSemantics := by
  intro op childExprs expr env v hrecon hlen hchildren
  simp only [Extractable.reconstruct] at hrecon
  cases op with
  | diffChar p c =>
    simp only [reconstructAttack] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, AttackExpr.eval, NodeSemantics.evalOp, evalAttackOpAS]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, AttackOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, AttackOp.children,
               List.getElem_cons_zero] at h0
    rw [h0]
  | truncatedDiff ab c =>
    simp only [reconstructAttack] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, AttackExpr.eval, NodeSemantics.evalOp, evalAttackOpAS]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, AttackOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, AttackOp.children,
               List.getElem_cons_zero] at h0
    rw [h0]
  | boomerang c1 c2 =>
    simp only [reconstructAttack] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, AttackExpr.eval, NodeSemantics.evalOp, evalAttackOpAS]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, AttackOp.children])
    have h1 := hchildren 1 (by simp) (by simp [NodeOps.children, AttackOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, AttackOp.children,
               List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
    rw [h0, h1]
  | impossible r c =>
    simp only [reconstructAttack] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, AttackExpr.eval, NodeSemantics.evalOp, evalAttackOpAS]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, AttackOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, AttackOp.children,
               List.getElem_cons_zero] at h0
    rw [h0]
  | linearTrail b c =>
    simp only [reconstructAttack] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, AttackExpr.eval, NodeSemantics.evalOp, evalAttackOpAS]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, AttackOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, AttackOp.children,
               List.getElem_cons_zero] at h0
    rw [h0]
  | linearHull nt c =>
    simp only [reconstructAttack] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, AttackExpr.eval, NodeSemantics.evalOp, evalAttackOpAS]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, AttackOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, AttackOp.children,
               List.getElem_cons_zero] at h0
    rw [h0]
  | algebraicRelation d c =>
    simp only [reconstructAttack] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, AttackExpr.eval, NodeSemantics.evalOp, evalAttackOpAS]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, AttackOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, AttackOp.children,
               List.getElem_cons_zero] at h0
    rw [h0]
  | grobnerStep c =>
    simp only [reconstructAttack] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, AttackExpr.eval, NodeSemantics.evalOp, evalAttackOpAS]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, AttackOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, AttackOp.children,
               List.getElem_cons_zero] at h0
    rw [h0]
  | meetInMiddle sr c1 c2 =>
    simp only [reconstructAttack] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, AttackExpr.eval, NodeSemantics.evalOp, evalAttackOpAS]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, AttackOp.children])
    have h1 := hchildren 1 (by simp) (by simp [NodeOps.children, AttackOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, AttackOp.children,
               List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
    rw [h0, h1]
  | rebound ir or_ c =>
    simp only [reconstructAttack] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, AttackExpr.eval, NodeSemantics.evalOp, evalAttackOpAS]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, AttackOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, AttackOp.children,
               List.getElem_cons_zero] at h0
    rw [h0]
  | compose f s =>
    simp only [reconstructAttack] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, AttackExpr.eval, NodeSemantics.evalOp, evalAttackOpAS]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, AttackOp.children])
    have h1 := hchildren 1 (by simp) (by simp [NodeOps.children, AttackOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, AttackOp.children,
               List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
    rw [h0, h1]
  | parallel l r =>
    simp only [reconstructAttack] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, AttackExpr.eval, NodeSemantics.evalOp, evalAttackOpAS]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, AttackOp.children])
    have h1 := hchildren 1 (by simp) (by simp [NodeOps.children, AttackOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, AttackOp.children,
               List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
    rw [h0, h1]
  | iterate n b =>
    simp only [reconstructAttack] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, AttackExpr.eval, NodeSemantics.evalOp, evalAttackOpAS]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, AttackOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, AttackOp.children,
               List.getElem_cons_zero] at h0
    rw [h0]
  | const v =>
    simp only [reconstructAttack] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp [EvalExpr.evalExpr, AttackExpr.eval, NodeSemantics.evalOp, evalAttackOpAS]

-- Smoke tests
#eval AttackExpr.eval (.diffChar 6 (.const 0)) (fun _ => default)
#check @attack_extractable_sound

end SuperHash
