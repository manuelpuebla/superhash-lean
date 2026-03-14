import SuperHash.Pareto.Extract

/-!
# SuperHash.Pareto.Soundness — Soundness of Pareto extraction

Provides:
- `extractPareto_all_correct`: every extracted design evaluates to the root value
- `extractPareto_no_dominated`: no design in the output is dominated by another

These two theorems compose with pipeline soundness to give the full SuperHash guarantee.
-/

namespace SuperHash

open UnionFind

set_option linter.unusedSimpArgs false

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Helper lemmas for list filtering
-- ══════════════════════════════════════════════════════════════════

/-- Elements of dedup are elements of the original list. -/
theorem dedup_subset (l : List (CryptoExpr × SecurityMetrics)) :
    ∀ x ∈ dedup l, x ∈ l := by
  suffices h : ∀ (acc : List (CryptoExpr × SecurityMetrics))
    (remaining : List (CryptoExpr × SecurityMetrics)),
    (∀ y ∈ acc, y ∈ l) →
    (∀ y ∈ remaining, y ∈ l) →
    ∀ y ∈ remaining.foldl (fun acc' p =>
      if acc'.any (fun q => q.2 == p.2) then acc' else acc' ++ [p]) acc,
    y ∈ l by
    exact h [] l (fun _ h => absurd h (by simp)) (fun y hy => hy)
  intro acc remaining hacc hrem
  induction remaining generalizing acc with
  | nil => simpa using hacc
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    split
    · exact ih acc hacc (fun y hy => hrem y (List.mem_cons.mpr (Or.inr hy)))
    · apply ih
      · intro y hy
        simp [List.mem_append, List.mem_singleton] at hy
        rcases hy with h | h
        · exact hacc y h
        · exact h ▸ hrem hd (List.mem_cons.mpr (Or.inl rfl))
      · intro y hy
        exact hrem y (List.mem_cons.mpr (Or.inr hy))

-- ══════════════════════════════════════════════════════════════════
-- Section 1b: Length bounds for dedup and extractPareto
-- ══════════════════════════════════════════════════════════════════

private theorem dedup_foldl_length_le (acc : List (CryptoExpr × SecurityMetrics))
    (remaining : List (CryptoExpr × SecurityMetrics)) :
    (remaining.foldl (fun acc' p =>
      if acc'.any (fun q => q.2 == p.2) then acc' else acc' ++ [p]) acc).length
    ≤ acc.length + remaining.length := by
  induction remaining generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.length_cons]
    split
    · calc _ ≤ acc.length + tl.length := ih acc
        _ ≤ acc.length + (tl.length + 1) := by omega
    · calc _ ≤ (acc ++ [hd]).length + tl.length := ih (acc ++ [hd])
        _ = (acc.length + 1) + tl.length := by simp [List.length_append]
        _ ≤ acc.length + (tl.length + 1) := by omega

/-- dedup never increases the length of the list. -/
theorem dedup_length_le (l : List (CryptoExpr × SecurityMetrics)) :
    (dedup l).length ≤ l.length := by
  unfold dedup
  have h := dedup_foldl_length_le [] l
  simp at h
  exact h

/-- **Output size bound**: the pipeline output has at most as many designs as weight vectors. -/
theorem extractPareto_length_le (g : EGraph CryptoOp) (weights : List Weights) (costFuel : Nat)
    (rootId : EClassId) :
    (extractPareto g weights costFuel rootId).length ≤ weights.length := by
  simp only [extractPareto]
  calc (((dedup (extractAll g weights costFuel rootId)).filter _).length)
      ≤ (dedup (extractAll g weights costFuel rootId)).length := List.length_filter_le _ _
    _ ≤ (extractAll g weights costFuel rootId).length := dedup_length_le _
    _ ≤ weights.length := extractAll_length_le g weights costFuel rootId

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Semantic correctness of Pareto extraction
-- ══════════════════════════════════════════════════════════════════

/-- **Every design in the Pareto extraction evaluates to the root value.**
    Follows from extractAll_correct + dedup/filter preserving the property. -/
theorem extractPareto_all_correct (g : EGraph CryptoOp) (weights : List Weights)
    (costFuel : Nat) (rootId : EClassId)
    (env : Nat → Nat) (v : EClassId → Nat)
    (hcv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (hsound : ExtractableSound CryptoOp CryptoExpr Nat) :
    ∀ p ∈ extractPareto g weights costFuel rootId,
      EvalExpr.evalExpr p.1 env = v (root g.unionFind rootId) := by
  intro p hp
  simp only [extractPareto] at hp
  rw [List.mem_filter] at hp
  obtain ⟨hp_dedup, _⟩ := hp
  -- p is in dedup (extractAll ...), hence in extractAll ...
  have hp_all := dedup_subset (extractAll g weights costFuel rootId) p hp_dedup
  exact extractAll_correct g weights costFuel env v hcv hwf hbni hsound rootId p hp_all

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Pareto property — no dominated designs
-- ══════════════════════════════════════════════════════════════════

/-- Helper: decide equality reflects equality. -/
private theorem decide_eq_of_true {α : Type} [DecidableEq α] (a b : α)
    (h : decide (a = b) = true) : a = b := by
  simp [decide_eq_true_eq] at h
  exact h

/-- **No design in the Pareto extraction is dominated by another.**
    The Pareto filter removes all dominated designs. -/
theorem extractPareto_no_dominated (g : EGraph CryptoOp) (weights : List Weights)
    (costFuel : Nat) (rootId : EClassId) :
    ∀ p1 ∈ extractPareto g weights costFuel rootId,
    ∀ p2 ∈ extractPareto g weights costFuel rootId,
      p1 ≠ p2 → ¬ dominates p1.2 p2.2 := by
  intro p1 hp1 p2 hp2 _hneq hdom
  simp only [extractPareto] at hp1 hp2
  let unique := dedup (extractAll g weights costFuel rootId)
  let frontMetrics := paretoFront (unique.map (·.2))
  -- p2 is in the filtered list: its metrics are in frontMetrics
  rw [List.mem_filter] at hp2
  obtain ⟨hp2_unique, hp2_front⟩ := hp2
  rw [List.any_eq_true] at hp2_front
  obtain ⟨m2, hm2_in, hm2_eq⟩ := hp2_front
  have hm2_is : m2 = p2.2 := decide_eq_of_true m2 p2.2 hm2_eq
  subst hm2_is
  -- p1 is in unique → p1.2 is in unique.map (·.2)
  rw [List.mem_filter] at hp1
  obtain ⟨hp1_unique, _⟩ := hp1
  have hp1_in_map : p1.2 ∈ unique.map (·.2) := List.mem_map.mpr ⟨p1, hp1_unique, rfl⟩
  -- p2.2 is in frontMetrics, but p1.2 dominates p2.2 — contradiction
  have hno_dom := paretoFront_no_dominated (unique.map (·.2)) p2.2 hm2_in
  exact hno_dom ⟨p1.2, hp1_in_map, hdom⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Metrics correctness — p.2 = p.1.metrics
-- ══════════════════════════════════════════════════════════════════

/-- **Metrics bridge**: every design in the Pareto extraction has p.2 = p.1.metrics.
    The metrics field is always computed from the expression, not independently. -/
theorem extractPareto_metrics_correct (g : EGraph CryptoOp) (weights : List Weights)
    (costFuel : Nat) (rootId : EClassId) :
    ∀ p ∈ extractPareto g weights costFuel rootId, p.2 = p.1.metrics := by
  intro p hp
  simp only [extractPareto] at hp
  rw [List.mem_filter] at hp
  obtain ⟨hp_dedup, _⟩ := hp
  have hp_all := dedup_subset (extractAll g weights costFuel rootId) p hp_dedup
  exact extractAll_metrics_eq g weights costFuel rootId p hp_all

-- Smoke test: properties type-check
#check @extractPareto_all_correct
#check @extractPareto_no_dominated
#check @extractPareto_metrics_correct

end SuperHash
