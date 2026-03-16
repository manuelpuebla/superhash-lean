import SuperHash.DesignLoop.Soundness
import SuperHash.Pipeline.Saturate
import SuperHash.Pipeline.Soundness

/-!
# SuperHash.Pipeline.MasterTheoremV2 — v2.0/v4.5.2 Master Theorem (N3.10)

Bundles the v2.0 + v4.5.2 guarantees into a single master theorem:
1. Termination: design loop always terminates (fuel-bounded)
2. Pool soundness: all rules remain kernel-verified
3. **Semantic correctness (v4.5.2 N5)**: CV + PMI + BNI preserved for the final e-graph

v4.5.1: Part 3 added via `saturateF_preserves_quadruple` by induction on fuel.
v4.5.2 C1: Extended to return full tuple (CV, PMI, BNI) via `designLoop_preserves_full`.
v4.5.2 C2: Corollary discharging `h_rules` for PatternSoundRule-based rules.
-/

namespace SuperHash

-- ============================================================
-- Helpers
-- ============================================================

/-- Graph of designLoopStep: equals saturateF when fuel > 0. -/
private theorem designLoopStep_graph_eq (state : DesignLoopState) (n : Nat)
    (hf : state.fuel = n + 1) :
    (designLoopStep state).graph =
    saturateF 10 5 3 state.graph
      (cryptoPatternRules.map (·.rule) ++ expansionRules) := by
  simp [designLoopStep, hf]

-- ============================================================
-- Semantic preservation through the loop (v4.5.2 full)
-- ============================================================

/-- DesignLoop preserves the full tuple: CV + PMI + BNI.
    v4.5.2 C1: extends `designLoop_preserves_cv` to also carry PMI and BNI.
    At each step:
    - CV + PMI + SHI + HCB: from `saturateF_preserves_quadruple`
    - BNI: from `saturateF_preserves_bni` -/
private theorem designLoop_preserves_full (state : DesignLoopState)
    (env : Nat → Nat) (v : EClassId → Nat)
    (hcv : ConsistentValuation state.graph env v)
    (hpmi : PostMergeInvariant state.graph)
    (hshi : SemanticHashconsInv state.graph env v)
    (hhcb : HashconsChildrenBounded state.graph)
    (hbni : BestNodeInv state.graph.classes)
    (h_rules : ∀ rule ∈ (cryptoPatternRules.map (·.rule) ++ expansionRules :
        List (RewriteRule CryptoOp)), PreservesCV env (applyRuleF 10 · rule)) :
    ∃ v_sat, ConsistentValuation (designLoop state).graph env v_sat ∧
      PostMergeInvariant (designLoop state).graph ∧
      BestNodeInv (designLoop state).graph.classes := by
  unfold designLoop
  split
  · -- fuel = 0: state unchanged
    exact ⟨v, hcv, hpmi, hbni⟩
  · -- fuel = n+1: step + recurse
    rename_i fuel heq
    -- Step: saturateF preserves quadruple (CV, PMI, SHI, HCB)
    have h_graph := designLoopStep_graph_eq state fuel heq
    obtain ⟨v', hcv', hpmi', hshi', hhcb'⟩ :=
      saturateF_preserves_quadruple 10 5 3 state.graph
        (cryptoPatternRules.map (·.rule) ++ expansionRules)
        env v hcv hpmi hshi hhcb h_rules
    -- BNI preservation through saturateF
    have hbni' := saturateF_preserves_bni 10 5 3 state.graph
      (cryptoPatternRules.map (·.rule) ++ expansionRules) hbni
    -- Rewrite to reference (designLoopStep state).graph
    rw [← h_graph] at hcv' hpmi' hshi' hhcb' hbni'
    -- Recurse (fuel decreases strictly)
    exact designLoop_preserves_full (designLoopStep state) env v'
      hcv' hpmi' hshi' hhcb' hbni' h_rules
termination_by state.fuel
decreasing_by
  simp_wf
  exact designLoopStep_fuel_decreasing state (by omega)

-- ============================================================
-- Master Theorem v2.0/v4.5.2
-- ============================================================

/-- SuperHash v2.0/v4.5.2 Master Theorem.

    Given an initial design loop state with:
    - A rule pool where all rules are verified (pool soundness)
    - A consistent valuation for the initial e-graph
    - BestNodeInv on the initial graph
    - Rules that preserve consistent valuation

    The design loop guarantees:
    1. **Termination**: final fuel = 0 (loop always completes)
    2. **Pool soundness**: all rules remain kernel-verified
    3. **Semantic correctness (v4.5.2 N5)**: CV + PMI + BNI preserved,
       enabling downstream extraction via `extractPareto_all_correct_cs` -/
theorem designLoop_master (state : DesignLoopState)
    (h_pool_sound : ∀ vr ∈ state.pool.rules, ∀ env : Nat → Nat,
      vr.candidate.lhsTemplate.eval env = vr.candidate.rhsTemplate.eval env)
    (env : Nat → Nat) (v : EClassId → Nat)
    (h_cv : ConsistentValuation state.graph env v)
    (h_pmi : PostMergeInvariant state.graph)
    (h_shi : SemanticHashconsInv state.graph env v)
    (h_hcb : HashconsChildrenBounded state.graph)
    (h_bni : BestNodeInv state.graph.classes)
    (h_rules : ∀ rule ∈ (cryptoPatternRules.map (·.rule) ++ expansionRules :
        List (RewriteRule CryptoOp)), PreservesCV env (applyRuleF 10 · rule)) :
    -- Part 1: Termination
    (designLoop state).fuel = 0 ∧
    -- Part 2: Pool soundness preserved
    (∀ vr ∈ (designLoop state).pool.rules, ∀ env' : Nat → Nat,
      vr.candidate.lhsTemplate.eval env' = vr.candidate.rhsTemplate.eval env') ∧
    -- Part 3: Semantic correctness — CV + PMI + BNI preserved
    (∃ v_sat, ConsistentValuation (designLoop state).graph env v_sat ∧
      PostMergeInvariant (designLoop state).graph ∧
      BestNodeInv (designLoop state).graph.classes) := by
  refine ⟨?_, ?_, ?_⟩
  · exact designLoop_fuel_zero state
  · intro vr hvr env'
    rw [designLoop_pool_eq state] at hvr
    exact h_pool_sound vr hvr env'
  · exact designLoop_preserves_full state env v h_cv h_pmi h_shi h_hcb h_bni h_rules

-- ============================================================
-- C2: Corollary — partial discharge of h_rules
-- ============================================================

/-- Corollary: for PatternSoundRule-based cryptoPatternRules, PreservesCV is automatically
    discharged via patternSoundRules_preserveCV. Only expansionRules need explicit hypothesis. -/
theorem designLoop_master_with_pattern_rules (state : DesignLoopState)
    (h_pool_sound : ∀ vr ∈ state.pool.rules, ∀ env : Nat → Nat,
      vr.candidate.lhsTemplate.eval env = vr.candidate.rhsTemplate.eval env)
    (env : Nat → Nat) (v : EClassId → Nat)
    (h_cv : ConsistentValuation state.graph env v)
    (h_pmi : PostMergeInvariant state.graph)
    (h_shi : SemanticHashconsInv state.graph env v)
    (h_hcb : HashconsChildrenBounded state.graph)
    (h_bni : BestNodeInv state.graph.classes)
    (h_expansion_cv : ∀ rule ∈ expansionRules,
        PreservesCV env (applyRuleF 10 · rule)) :
    -- Same conclusion as designLoop_master
    (designLoop state).fuel = 0 ∧
    (∀ vr ∈ (designLoop state).pool.rules, ∀ env' : Nat → Nat,
      vr.candidate.lhsTemplate.eval env' = vr.candidate.rhsTemplate.eval env') ∧
    (∃ v_sat, ConsistentValuation (designLoop state).graph env v_sat ∧
      PostMergeInvariant (designLoop state).graph ∧
      BestNodeInv (designLoop state).graph.classes) := by
  apply designLoop_master state h_pool_sound env v h_cv h_pmi h_shi h_hcb h_bni
  intro rule hrule
  rw [List.mem_append] at hrule
  rcases hrule with h_pattern | h_expansion
  · exact patternSoundRules_preserveCV 10 env cryptoPatternRules rule h_pattern
  · exact h_expansion_cv rule h_expansion

-- ============================================================
-- Convenience: run and verify
-- ============================================================

/-- Run the full v2.0 pipeline on a design with given fuel.
    Returns the final Pareto front with all guarantees. -/
def superhash_v2 (design : CryptoExpr) (fuel : Nat := 10) :
    List (CryptoExpr × SecurityMetrics) :=
  let state := DesignLoopState.init design fuel
  let final := designLoop state
  final.paretoFront

-- ============================================================
-- Non-vacuity example
-- ============================================================

/-- Non-vacuity: v2.0 pipeline runs and terminates on AES block. -/
example : (designLoop (DesignLoopState.init (.spnBlock 10 (.const 7) (.const 5)) 3)).fuel = 0 :=
  designLoop_fuel_zero _

/-- Non-vacuity: pool soundness for empty pool (trivial). -/
example : ∀ vr ∈ (RulePool.empty).rules, ∀ env : Nat → Nat,
    vr.candidate.lhsTemplate.eval env = vr.candidate.rhsTemplate.eval env :=
  fun _ h => nomatch h

-- ============================================================
-- Smoke test
-- ============================================================

#eval
  let result := superhash_v2 (.spnBlock 10 (.const 7) (.const 5)) (fuel := 3)
  s!"v2.0 pipeline: {result.length} Pareto-optimal designs"

end SuperHash
