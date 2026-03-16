import SuperHash.Pipeline.Extract
import SuperHash.Pipeline.Saturate
import SuperHash.Pipeline.EMatchSpec

/-!
# SuperHash.Pipeline.Soundness — End-to-end pipeline correctness

Provides:
- `optimizeF`: verified greedy pipeline (saturateF + computeCostsF + extractAuto)
- `optimizeF_soundness`: if optimizeF returns `some expr`, then `expr` evaluates to the
  semantic value of the root class in the saturated graph
- `saturateF_preserves_wf`: WellFormed preservation through saturation
- `optimizeF_soundness_complete`: auto-discharges hwf_sat and hbni_sat hypotheses

Pattern: Three-Tier Bridge (L-513)
-/

namespace SuperHash

open UnionFind

variable {Op : Type} {Val : Type} {Expr : Type}
  [NodeOps Op] [BEq Op] [Hashable Op]
  [LawfulBEq Op] [LawfulHashable Op]
  [DecidableEq Op] [Repr Op] [Inhabited Op]
  [NodeSemantics Op Val]
  [Extractable Op Expr] [EvalExpr Expr Val]

set_option linter.unusedSectionVars false

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Verified Pipeline Function
-- ══════════════════════════════════════════════════════════════════

/-- Verified greedy optimization pipeline.
    Composes `saturateF` + `computeCostsF` + `extractAuto` — all total, verified functions.

    Parameters:
    - `fuel`: fuel for ematch/instantiate within each saturation step
    - `maxIter`: maximum saturation iterations
    - `rebuildFuel`: fuel for rebuild within each saturation step
    - `costFn`: node cost function for extraction
    - `costFuel`: iterations for cost convergence -/
def optimizeF (fuel maxIter rebuildFuel : Nat)
    (g : EGraph Op) (rules : List (RewriteRule Op))
    (costFn : ENode Op → Nat) (costFuel : Nat)
    (rootId : EClassId) : Option Expr :=
  let g_sat := saturateF fuel maxIter rebuildFuel g rules
  let g_cost := computeCostsF g_sat costFn costFuel
  extractAuto g_cost rootId

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Helper — PatternSoundRules imply PreservesCV
-- ══════════════════════════════════════════════════════════════════

/-- PatternSoundRules imply PreservesCV for each rewrite rule.
    Factors the h_rules construction from saturateF_preserves_consistent_internal. -/
theorem patternSoundRules_preserveCV [Inhabited Val] (fuel : Nat) (env : Nat → Val)
    (rules : List (PatternSoundRule Op Val)) :
    ∀ rule ∈ rules.map (·.rule), PreservesCV env (applyRuleF fuel · rule) := by
  have hematch_bnd : ∀ (g' : EGraph Op) (rule : PatternSoundRule Op Val),
      rule ∈ rules → PostMergeInvariant g' →
      ∀ (classId : EClassId), classId < g'.unionFind.parent.size →
      ∀ σ ∈ ematchF fuel g' rule.rule.lhs classId,
      ∀ pv id, σ.get? pv = some id → id < g'.unionFind.parent.size :=
    fun g' _rule _hrule hpmi' classId hclass σ hmem pv id hσ =>
      ematchF_substitution_bounded g' hpmi' fuel _rule.rule.lhs classId ∅ hclass
        (fun pv' id' h => absurd h (by rw [Std.HashMap.get?_eq_getElem?]; simp))
        σ hmem pv id hσ
  intro rule hrule
  obtain ⟨psrule, hps, hrw⟩ := List.mem_map.mp hrule
  rw [← hrw]
  intro g' v' hcv' hpmi' hshi' hhcb'
  simp only [applyRuleF]
  suffices h : ∀ (l : List EClassId) (acc : EGraph Op) (v_acc : EClassId → Val),
    (∀ cid ∈ l, cid < g'.unionFind.parent.size) →
    ConsistentValuation acc env v_acc → PostMergeInvariant acc →
    SemanticHashconsInv acc env v_acc → HashconsChildrenBounded acc →
    g'.unionFind.parent.size ≤ acc.unionFind.parent.size →
    ∃ v'', ConsistentValuation (l.foldl (fun acc classId =>
      applyRuleAtF fuel acc psrule.rule classId) acc) env v'' ∧
      PostMergeInvariant (l.foldl (fun acc classId =>
        applyRuleAtF fuel acc psrule.rule classId) acc) ∧
      SemanticHashconsInv (l.foldl (fun acc classId =>
        applyRuleAtF fuel acc psrule.rule classId) acc) env v'' ∧
      HashconsChildrenBounded (l.foldl (fun acc classId =>
        applyRuleAtF fuel acc psrule.rule classId) acc) by
    obtain ⟨v'', hcv'', hpmi'', hshi'', hhcb''⟩ := h _ g' v'
      (fun cid hcid => by
        have ⟨a, hmem, ha_eq⟩ : ∃ a ∈ g'.classes.toList, a.1 = cid :=
          List.mem_map.mp hcid
        have hcont : g'.classes.contains a.fst = true := by
          rw [Std.HashMap.contains_eq_isSome_getElem?,
              Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hmem]; rfl
        exact ha_eq ▸ hpmi'.classes_entries_valid a.fst hcont)
      hcv' hpmi' hshi' hhcb' Nat.le.refl
    exact ⟨v'', hcv'', hpmi'', hshi'', hhcb''⟩
  intro l
  induction l with
  | nil =>
    intro acc v_acc _ hcv hpmi hshi hhcb _
    exact ⟨v_acc, hcv, hpmi, hshi, hhcb⟩
  | cons cid rest ih =>
    intro acc v_acc hbnd hcv_acc hpmi_acc hshi_acc hhcb_acc hsize_acc
    simp only [List.foldl_cons]
    have hcid : cid < acc.unionFind.parent.size :=
      Nat.lt_of_lt_of_le (hbnd cid (.head _)) hsize_acc
    obtain ⟨v'', hcv'', hpmi'', hshi'', hhcb'', hsize''⟩ :=
      applyRuleAtF_sound fuel psrule cid env sameShapeSemantics_holds
        (InstantiateEvalSound_holds env) acc v_acc hcv_acc hpmi_acc
        hshi_acc hhcb_acc hcid (hematch_bnd acc psrule hps hpmi_acc cid hcid)
    exact ih _ v'' (fun c hc => hbnd c (.tail _ hc)) hcv'' hpmi'' hshi'' hhcb''
      (Nat.le_trans hsize_acc hsize'')

-- ══════════════════════════════════════════════════════════════════
-- Section 3: saturateF preserves WellFormed
-- ══════════════════════════════════════════════════════════════════

/-- saturateF preserves WellFormed. Derives WellFormed from PMI preservation
    through the saturation pipeline. Corollary of `saturateF_preserves_quadruple`. -/
theorem saturateF_preserves_wf [Inhabited Val] (fuel maxIter rebuildFuel : Nat)
    (g : EGraph Op) (rules : List (PatternSoundRule Op Val))
    (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g) (hshi : SemanticHashconsInv g env v)
    (hhcb : HashconsChildrenBounded g) :
    WellFormed (saturateF fuel maxIter rebuildFuel g (rules.map (·.rule))).unionFind :=
  let ⟨_, _, hpmi_sat, _, _⟩ := saturateF_preserves_quadruple fuel maxIter rebuildFuel g
    (rules.map (·.rule)) env v hcv hpmi hshi hhcb
    (patternSoundRules_preserveCV fuel env rules)
  hpmi_sat.uf_wf

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Greedy pipeline soundness
-- ══════════════════════════════════════════════════════════════════

/-- **Greedy pipeline soundness.** If `optimizeF` returns `some expr`, then
    `expr` evaluates to the semantic value of the root class in the saturated graph.

    Composes: saturateF_preserves_consistent_internal + computeCostsF_extractF_correct.

    Hypotheses:
    - ConsistentValuation, PostMergeInvariant, SemanticHashconsInv, HashconsChildrenBounded on initial graph
    - WellFormed and BestNodeInv on saturated graph (discharged in _complete variant)
    - ExtractableSound for the expression type -/
theorem optimizeF_soundness [Inhabited Val] (g : EGraph Op)
    (rules : List (PatternSoundRule Op Val))
    (costFn : ENode Op → Nat) (costFuel fuel maxIter rebuildFuel : Nat)
    (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g) (hshi : SemanticHashconsInv g env v)
    (hhcb : HashconsChildrenBounded g)
    (rootId : EClassId) (expr : Expr)
    (hwf_sat : WellFormed (saturateF fuel maxIter rebuildFuel g
      (rules.map (·.rule))).unionFind)
    (hbni_sat : BestNodeInv (saturateF fuel maxIter rebuildFuel g
      (rules.map (·.rule))).classes)
    (hsound : ExtractableSound Op Expr Val)
    (hopt : optimizeF fuel maxIter rebuildFuel g (rules.map (·.rule))
      costFn costFuel rootId = some expr) :
    ∃ (v_sat : EClassId → Val), EvalExpr.evalExpr expr env =
      v_sat (root (saturateF fuel maxIter rebuildFuel g
        (rules.map (·.rule))).unionFind rootId) := by
  -- Step 1: Get consistent valuation for the saturated graph
  obtain ⟨v_sat, hcv_sat⟩ := saturateF_preserves_consistent_internal fuel maxIter
    rebuildFuel g rules env v hcv hpmi hshi hhcb sameShapeSemantics_holds
    (InstantiateEvalSound_holds env)
    (fun g' rule hrule hpmi' classId hclass σ hmem pv id hσ =>
      ematchF_substitution_bounded g' hpmi' fuel rule.rule.lhs classId ∅ hclass
        (fun pv' id' h => absurd h (by rw [Std.HashMap.get?_eq_getElem?]; simp))
        σ hmem pv id hσ)
  -- Step 2: Unfold optimizeF to see the pipeline stages
  unfold optimizeF at hopt
  -- Step 3: computeCostsF preserves consistency, WF, BNI
  let g_sat := saturateF fuel maxIter rebuildFuel g (rules.map (·.rule))
  have hcv_cost := computeCostsF_preserves_consistency g_sat costFn costFuel env v_sat hcv_sat
  have hbni_cost := computeCostsF_bestNode_in_nodes g_sat costFn costFuel hbni_sat
  have hwf_cost : WellFormed (computeCostsF g_sat costFn costFuel).unionFind := by
    rw [computeCostsF_preserves_uf]; exact hwf_sat
  -- Step 4: extractAuto is correct on cost graph
  have hresult := extractAuto_correct (computeCostsF g_sat costFn costFuel)
    env v_sat hcv_cost hwf_cost hbni_cost hsound rootId expr hopt
  -- Step 5: Root is preserved through cost computation
  have hroot : root (computeCostsF g_sat costFn costFuel).unionFind rootId =
    root g_sat.unionFind rootId := by
    simp [computeCostsF_preserves_uf]
  rw [hroot] at hresult
  exact ⟨v_sat, hresult⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Hypothesis-free greedy pipeline soundness
-- ══════════════════════════════════════════════════════════════════

/-- **Hypothesis-free greedy pipeline soundness.** Like `optimizeF_soundness` but
    auto-discharges `hwf_sat` and `hbni_sat` from initial e-graph invariants.

    The only new hypothesis compared to `optimizeF_soundness` is `hbni_init`,
    which states that the initial e-graph satisfies BestNodeInv. This is trivially
    true for freshly constructed graphs (all classes have `bestNode := none`). -/
theorem optimizeF_soundness_complete [Inhabited Val] (g : EGraph Op)
    (rules : List (PatternSoundRule Op Val))
    (costFn : ENode Op → Nat) (costFuel fuel maxIter rebuildFuel : Nat)
    (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g) (hshi : SemanticHashconsInv g env v)
    (hhcb : HashconsChildrenBounded g)
    (hbni_init : BestNodeInv g.classes)
    (rootId : EClassId) (expr : Expr)
    (hsound : ExtractableSound Op Expr Val)
    (hopt : optimizeF fuel maxIter rebuildFuel g (rules.map (·.rule))
      costFn costFuel rootId = some expr) :
    ∃ (v_sat : EClassId → Val), EvalExpr.evalExpr expr env =
      v_sat (root (saturateF fuel maxIter rebuildFuel g
        (rules.map (·.rule))).unionFind rootId) :=
  optimizeF_soundness g rules costFn costFuel fuel maxIter rebuildFuel env v
    hcv hpmi hshi hhcb rootId expr
    (saturateF_preserves_wf fuel maxIter rebuildFuel g rules env v hcv hpmi hshi hhcb)
    (saturateF_preserves_bni fuel maxIter rebuildFuel g (rules.map (·.rule)) hbni_init)
    hsound hopt

-- Smoke test: optimizeF type-checks
#check @optimizeF

end SuperHash
