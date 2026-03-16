import SuperHash.DesignLoop.Soundness
import SuperHash.Pipeline.Saturate

/-!
# SuperHash.Pipeline.MasterTheoremV2 — v2.0/v4.5.1 Master Theorem (N3.10)

Bundles the v2.0 + v4.5.1 guarantees into a single master theorem:
1. Termination: design loop always terminates (fuel-bounded)
2. Pool soundness: all rules remain kernel-verified
3. **Semantic correctness (v4.5.1 N5)**: a consistent valuation exists for the final e-graph

v4.5.1: Part 3 added via `saturateF_preserves_quadruple` by induction on fuel.
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
-- Semantic preservation through the loop (v4.5.1 N5)
-- ============================================================

/-- DesignLoop preserves the existence of a consistent valuation.
    v4.5.1 N5: by induction on fuel, applying saturateF_preserves_quadruple
    at each designLoopStep. -/
private theorem designLoop_preserves_cv (state : DesignLoopState)
    (env : Nat → Nat) (v : EClassId → Nat)
    (hcv : ConsistentValuation state.graph env v)
    (hpmi : PostMergeInvariant state.graph)
    (hshi : SemanticHashconsInv state.graph env v)
    (hhcb : HashconsChildrenBounded state.graph)
    (h_rules : ∀ rule ∈ (cryptoPatternRules.map (·.rule) ++ expansionRules :
        List (RewriteRule CryptoOp)), PreservesCV env (applyRuleF 10 · rule)) :
    ∃ v', ConsistentValuation (designLoop state).graph env v' := by
  unfold designLoop
  split
  · -- fuel = 0: state unchanged
    exact ⟨v, hcv⟩
  · -- fuel = n+1: step + recurse
    rename_i fuel heq
    -- Step: saturateF preserves quadruple
    have h_graph := designLoopStep_graph_eq state fuel heq
    obtain ⟨v', hcv', hpmi', hshi', hhcb'⟩ :=
      saturateF_preserves_quadruple 10 5 3 state.graph
        (cryptoPatternRules.map (·.rule) ++ expansionRules)
        env v hcv hpmi hshi hhcb h_rules
    -- Rewrite to reference (designLoopStep state).graph
    rw [← h_graph] at hcv' hpmi' hshi' hhcb'
    -- Recurse (fuel decreases strictly)
    exact designLoop_preserves_cv (designLoopStep state) env v' hcv' hpmi' hshi' hhcb' h_rules
termination_by state.fuel
decreasing_by
  simp_wf
  exact designLoopStep_fuel_decreasing state (by omega)

-- ============================================================
-- Master Theorem v2.0/v4.5.1
-- ============================================================

/-- SuperHash v2.0/v4.5.1 Master Theorem.

    Given an initial design loop state with:
    - A rule pool where all rules are verified (pool soundness)
    - A consistent valuation for the initial e-graph (v4.5.1)
    - Rules that preserve consistent valuation

    The design loop guarantees:
    1. **Termination**: final fuel = 0 (loop always completes)
    2. **Pool soundness**: all rules remain kernel-verified
    3. **Semantic correctness (v4.5.1 N5)**: a consistent valuation exists
       for the final e-graph -/
theorem designLoop_master (state : DesignLoopState)
    (h_pool_sound : ∀ vr ∈ state.pool.rules, ∀ env : Nat → Nat,
      vr.candidate.lhsTemplate.eval env = vr.candidate.rhsTemplate.eval env)
    (env : Nat → Nat) (v : EClassId → Nat)
    (h_cv : ConsistentValuation state.graph env v)
    (h_pmi : PostMergeInvariant state.graph)
    (h_shi : SemanticHashconsInv state.graph env v)
    (h_hcb : HashconsChildrenBounded state.graph)
    (h_rules : ∀ rule ∈ (cryptoPatternRules.map (·.rule) ++ expansionRules :
        List (RewriteRule CryptoOp)), PreservesCV env (applyRuleF 10 · rule)) :
    -- Part 1: Termination
    (designLoop state).fuel = 0 ∧
    -- Part 2: Pool soundness preserved
    (∀ vr ∈ (designLoop state).pool.rules, ∀ env' : Nat → Nat,
      vr.candidate.lhsTemplate.eval env' = vr.candidate.rhsTemplate.eval env') ∧
    -- Part 3: Semantic correctness (v4.5.1 N5)
    (∃ v_sat, ConsistentValuation (designLoop state).graph env v_sat) := by
  refine ⟨?_, ?_, ?_⟩
  · exact designLoop_fuel_zero state
  · intro vr hvr env'
    rw [designLoop_pool_eq state] at hvr
    exact h_pool_sound vr hvr env'
  · exact designLoop_preserves_cv state env v h_cv h_pmi h_shi h_hcb h_rules

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
