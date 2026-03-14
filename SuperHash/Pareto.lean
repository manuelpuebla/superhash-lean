import SuperHash.DesignParams

/-!
# SuperHash.Pareto — Pareto dominance for multi-objective optimization

Defines the Pareto dominance relation on SecurityMetrics and proves
irreflexivity, transitivity, asymmetry. Provides `paretoFront` filter
and its correctness theorem.

Adapted from LeanHash.DesignSpace.
-/

namespace SuperHash

/-- Pareto dominance: `a` dominates `b` if `a` is at least as good
    in all objectives AND strictly better in at least one. -/
def dominates (a b : SecurityMetrics) : Prop :=
  a.securityBits ≥ b.securityBits ∧
  a.latency ≤ b.latency ∧
  a.gateCount ≤ b.gateCount ∧
  (a.securityBits > b.securityBits ∨ a.latency < b.latency ∨ a.gateCount < b.gateCount)

/-- Pareto dominance is irreflexive. -/
theorem dominates_irrefl (a : SecurityMetrics) : ¬ dominates a a := by
  intro ⟨_, _, _, h4⟩
  rcases h4 with h | h | h <;> omega

/-- Pareto dominance is transitive. -/
theorem dominates_trans (a b c : SecurityMetrics) :
    dominates a b → dominates b c → dominates a c := by
  intro ⟨h1, h2, h3, h4⟩ ⟨h5, h6, h7, _h8⟩
  refine ⟨by omega, by omega, by omega, ?_⟩
  rcases h4 with h | h | h
  · left; omega
  · right; left; omega
  · right; right; omega

/-- Pareto dominance is asymmetric. -/
theorem dominates_asymm (a b : SecurityMetrics) :
    dominates a b → ¬ dominates b a := by
  intro ⟨h1, h2, h3, h4⟩ ⟨h5, h6, h7, h8⟩
  rcases h4 with h | h | h
  · rcases h8 with h' | h' | h' <;> omega
  · rcases h8 with h' | h' | h' <;> omega
  · rcases h8 with h' | h' | h' <;> omega

/-- Bool version of `dominates` for computation. -/
def dominatesBool (a b : SecurityMetrics) : Bool :=
  a.securityBits ≥ b.securityBits &&
  a.latency ≤ b.latency &&
  a.gateCount ≤ b.gateCount &&
  (a.securityBits > b.securityBits || a.latency < b.latency || a.gateCount < b.gateCount)

/-- Bool-Prop bridge: dominatesBool reflects dominates. -/
theorem dominatesBool_eq_true_iff (a b : SecurityMetrics) :
    dominatesBool a b = true ↔ dominates a b := by
  constructor
  · intro h
    simp [dominatesBool, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine ⟨h1, h2, h3, ?_⟩
    rcases h4 with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · intro ⟨h1, h2, h3, h4⟩
    simp [dominatesBool, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
    rcases h4 with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

/-- Is a metric dominated by any in a list? -/
def isDominatedBy (m : SecurityMetrics) (ms : List SecurityMetrics) : Bool :=
  ms.any (fun m' => dominatesBool m' m)

/-- Filter to the Pareto front: remove all dominated designs. -/
def paretoFront (ms : List SecurityMetrics) : List SecurityMetrics :=
  ms.filter (fun m => !isDominatedBy m ms)

/-- Every element of paretoFront is not dominated by any element of the input. -/
theorem paretoFront_no_dominated (ms : List SecurityMetrics) :
    ∀ m ∈ paretoFront ms, ¬ ∃ m' ∈ ms, dominates m' m := by
  intro m hm ⟨m', hm'_in, hm'_dom⟩
  rw [paretoFront, List.mem_filter] at hm
  obtain ⟨_, hnd⟩ := hm
  have hdom_bool : dominatesBool m' m = true := (dominatesBool_eq_true_iff m' m).mpr hm'_dom
  have hany : isDominatedBy m ms = true := by
    simp [isDominatedBy, List.any_eq_true]
    exact ⟨m', hm'_in, hdom_bool⟩
  simp [hany] at hnd

/-- Every non-dominated element of the input is in the Pareto front. -/
theorem paretoFront_complete (ms : List SecurityMetrics) :
    ∀ m ∈ ms, (¬ ∃ m' ∈ ms, dominates m' m) → m ∈ paretoFront ms := by
  intro m hm hnd
  rw [paretoFront, List.mem_filter]
  refine ⟨hm, ?_⟩
  suffices isDominatedBy m ms = false by simp [this]
  rw [Bool.eq_false_iff]
  intro hany
  rw [isDominatedBy, List.any_eq_true] at hany
  obtain ⟨m', hm'_in, hm'_dom⟩ := hany
  rw [dominatesBool_eq_true_iff] at hm'_dom
  exact hnd ⟨m', hm'_in, hm'_dom⟩

-- Smoke tests
#eval paretoFront [⟨128, 10, 1000⟩, ⟨64, 20, 2000⟩, ⟨128, 15, 500⟩]
-- Expected: [⟨128, 10, 1000⟩, ⟨128, 15, 500⟩] — the 64-bit design is dominated

end SuperHash
