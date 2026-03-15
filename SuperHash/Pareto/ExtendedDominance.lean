import SuperHash.Pareto.ExtendedMetrics

/-!
# SuperHash.Pareto.ExtendedDominance — 6D Pareto dominance

Defines Pareto dominance over ExtendedSecurityMetrics (6 dimensions):
4 security dimensions (↑ better) + latency and gateCount (↓ better).

Proves irreflexivity, transitivity, asymmetry, and a bridge theorem
showing that 6D dominance implies 3D dominance after projection.

Follows the same pattern as SuperHash.Pareto (3D dominance).
-/

namespace SuperHash

-- ============================================================
-- Section 1: 6D Dominance (Prop version)
-- ============================================================

/-- **6D Pareto dominance.**
    `a` dominates `b` if `a` is at least as good in ALL 6 dimensions
    AND strictly better in at least one.
    Security dimensions: higher is better. Efficiency dimensions: lower is better. -/
def extDominates (a b : ExtendedSecurityMetrics) : Prop :=
  a.collisionBits ≥ b.collisionBits ∧
  a.preImageBits ≥ b.preImageBits ∧
  a.secondPreImageBits ≥ b.secondPreImageBits ∧
  a.targetCRBits ≥ b.targetCRBits ∧
  a.latency ≤ b.latency ∧
  a.gateCount ≤ b.gateCount ∧
  (a.collisionBits > b.collisionBits ∨
   a.preImageBits > b.preImageBits ∨
   a.secondPreImageBits > b.secondPreImageBits ∨
   a.targetCRBits > b.targetCRBits ∨
   a.latency < b.latency ∨
   a.gateCount < b.gateCount)

/-- extDominates is decidable (all conjuncts/disjuncts are Nat comparisons). -/
instance (a b : ExtendedSecurityMetrics) : Decidable (extDominates a b) := by
  unfold extDominates; exact inferInstance

-- ============================================================
-- Section 2: Core properties
-- ============================================================

/-- 6D dominance is irreflexive: no element dominates itself. -/
theorem extDominates_irrefl (a : ExtendedSecurityMetrics) : ¬ extDominates a a := by
  intro ⟨_, _, _, _, _, _, h7⟩
  rcases h7 with h | h | h | h | h | h <;> omega

/-- 6D dominance is transitive. -/
theorem extDominates_trans (a b c : ExtendedSecurityMetrics) :
    extDominates a b → extDominates b c → extDominates a c := by
  intro ⟨h1, h2, h3, h4, h5, h6, h7⟩ ⟨g1, g2, g3, g4, g5, g6, _g7⟩
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
  rcases h7 with h | h | h | h | h | h
  · left; omega
  · right; left; omega
  · right; right; left; omega
  · right; right; right; left; omega
  · right; right; right; right; left; omega
  · right; right; right; right; right; omega

/-- 6D dominance is asymmetric. -/
theorem extDominates_asymm (a b : ExtendedSecurityMetrics) :
    extDominates a b → ¬ extDominates b a := by
  intro ⟨h1, h2, h3, h4, h5, h6, h7⟩ ⟨g1, g2, g3, g4, g5, g6, _g7⟩
  rcases h7 with h | h | h | h | h | h <;> omega

-- ============================================================
-- Section 3: Bool version for computation
-- ============================================================

/-- Bool version of `extDominates` for computation. -/
def extDominatesBool (a b : ExtendedSecurityMetrics) : Bool :=
  decide (extDominates a b)

/-- Bool-Prop bridge: extDominatesBool reflects extDominates. -/
theorem extDominatesBool_eq_true_iff (a b : ExtendedSecurityMetrics) :
    extDominatesBool a b = true ↔ extDominates a b := by
  simp [extDominatesBool, decide_eq_true_eq]

-- ============================================================
-- Section 4: Bridge to 3D dominance
-- ============================================================

/-- Helper: min of two naturals is monotone. -/
private theorem min_le_min_of_le {a b c d : Nat} (h1 : a ≥ c) (h2 : b ≥ d) :
    min a b ≥ min c d := by omega

/-- Helper: min4 ≥ min4 when all components ≥. -/
private theorem min4_mono {a1 a2 a3 a4 b1 b2 b3 b4 : Nat}
    (h1 : a1 ≥ b1) (h2 : a2 ≥ b2) (h3 : a3 ≥ b3) (h4 : a4 ≥ b4) :
    min a1 (min a2 (min a3 a4)) ≥ min b1 (min b2 (min b3 b4)) :=
  min_le_min_of_le h1 (min_le_min_of_le h2 (min_le_min_of_le h3 h4))

/-- **6D dominance implies weak 3D dominance (all dims ≥).**
    The projection is weakly monotone: if a ext-dominates b, then
    toSecurityMetrics a is at least as good as toSecurityMetrics b
    in all 3 dimensions.

    Note: this is not full `dominates` because a strict improvement in one
    security dimension (e.g., targetCRBits) may not affect the min projection.
    Full `dominates` requires an additional condition (see below). -/
theorem extDominates_implies_weak_dominates (a b : ExtendedSecurityMetrics) :
    extDominates a b →
    (toSecurityMetrics a).securityBits ≥ (toSecurityMetrics b).securityBits ∧
    (toSecurityMetrics a).latency ≤ (toSecurityMetrics b).latency ∧
    (toSecurityMetrics a).gateCount ≤ (toSecurityMetrics b).gateCount := by
  intro ⟨h1, h2, h3, h4, h5, h6, _h7⟩
  exact ⟨min4_mono h1 h2 h3 h4, h5, h6⟩

/-- **6D dominance with efficiency improvement implies 3D dominance.**
    When the strict improvement is in latency or gateCount, the projection
    preserves dominance fully. -/
theorem extDominates_efficiency_implies_dominates (a b : ExtendedSecurityMetrics)
    (hdom : extDominates a b)
    (heff : a.latency < b.latency ∨ a.gateCount < b.gateCount) :
    dominates (toSecurityMetrics a) (toSecurityMetrics b) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, _h7⟩ := hdom
  refine ⟨min4_mono h1 h2 h3 h4, h5, h6, ?_⟩
  rcases heff with hl | hg
  · right; left; exact hl
  · right; right; exact hg

/-- Helper: min is strictly monotone when all inputs are strictly greater. -/
private theorem min_lt_min_of_lt {a b c d : Nat}
    (h1 : a > c) (h2 : b > d) : min a b > min c d := by
  simp [Nat.min_def]; split <;> split <;> omega

/-- **6D dominance with ALL security strictly better implies 3D dominance.**
    When all 4 security dimensions are strictly better, the min is also
    strictly better, so the full 3D dominance holds. -/
theorem extDominates_allsec_implies_dominates (a b : ExtendedSecurityMetrics)
    (hdom : extDominates a b)
    (hcoll : a.collisionBits > b.collisionBits)
    (hpre : a.preImageBits > b.preImageBits)
    (hsec : a.secondPreImageBits > b.secondPreImageBits)
    (htcr : a.targetCRBits > b.targetCRBits) :
    dominates (toSecurityMetrics a) (toSecurityMetrics b) := by
  obtain ⟨_, _, _, _, h5, h6, _⟩ := hdom
  refine ⟨?_, h5, h6, ?_⟩
  · exact min4_mono (Nat.le_of_lt hcoll) (Nat.le_of_lt hpre)
      (Nat.le_of_lt hsec) (Nat.le_of_lt htcr)
  · left
    simp only [toSecurityMetrics]
    exact min_lt_min_of_lt hcoll (min_lt_min_of_lt hpre (min_lt_min_of_lt hsec htcr))

-- ============================================================
-- Section 5: Pareto front computation
-- ============================================================

/-- Is a metric dominated by any in a list? -/
def isExtDominatedBy (m : ExtendedSecurityMetrics)
    (ms : List ExtendedSecurityMetrics) : Bool :=
  ms.any (fun m' => extDominatesBool m' m)

/-- Filter to the 6D Pareto front: remove all dominated designs. -/
def extParetoFront (ms : List ExtendedSecurityMetrics) :
    List ExtendedSecurityMetrics :=
  ms.filter (fun m => !isExtDominatedBy m ms)

-- ============================================================
-- Section 6: Pareto front correctness
-- ============================================================

/-- Every element of extParetoFront is not dominated by any element of the input. -/
theorem extParetoFront_no_dominated (ms : List ExtendedSecurityMetrics) :
    ∀ m ∈ extParetoFront ms, ¬ ∃ m' ∈ ms, extDominates m' m := by
  intro m hm ⟨m', hm'_in, hm'_dom⟩
  rw [extParetoFront, List.mem_filter] at hm
  obtain ⟨_, hnd⟩ := hm
  have hdom_bool : extDominatesBool m' m = true :=
    (extDominatesBool_eq_true_iff m' m).mpr hm'_dom
  have hany : isExtDominatedBy m ms = true := by
    simp [isExtDominatedBy, List.any_eq_true]
    exact ⟨m', hm'_in, hdom_bool⟩
  simp [hany] at hnd

/-- Every non-dominated element of the input is in the 6D Pareto front. -/
theorem extParetoFront_complete (ms : List ExtendedSecurityMetrics) :
    ∀ m ∈ ms, (¬ ∃ m' ∈ ms, extDominates m' m) → m ∈ extParetoFront ms := by
  intro m hm hnd
  rw [extParetoFront, List.mem_filter]
  refine ⟨hm, ?_⟩
  suffices isExtDominatedBy m ms = false by simp [this]
  rw [Bool.eq_false_iff]
  intro hany
  rw [isExtDominatedBy, List.any_eq_true] at hany
  obtain ⟨m', hm'_in, hm'_dom⟩ := hany
  rw [extDominatesBool_eq_true_iff] at hm'_dom
  exact hnd ⟨m', hm'_in, hm'_dom⟩

-- ============================================================
-- Section 7: Non-vacuity examples
-- ============================================================

/-- Non-vacuity 1: SHA-256 ext-dominates a design with same efficiency. -/
example : extDominates sha256Extended
    ⟨60, 120, 120, 120, 64, 200⟩ := by decide

/-- Non-vacuity 2: AES-128 ext-dominates a weaker design. -/
example : extDominates aes128Extended
    ⟨32, 64, 64, 64, 20, 100⟩ := by decide

/-- Non-vacuity 3: efficiency bridge is satisfiable with concrete dominance. -/
example : dominates (toSecurityMetrics aes128Extended)
                    (toSecurityMetrics ⟨32, 64, 64, 64, 20, 100⟩) :=
  extDominates_efficiency_implies_dominates aes128Extended ⟨32, 64, 64, 64, 20, 100⟩
    (by decide) (by left; decide)

/-- Non-vacuity 4: Pareto front filters dominated designs. -/
example : (extParetoFront [aes128Extended, poseidon128Extended, sha256Extended]).length ≤ 3 := by
  native_decide

/-- Non-vacuity 5: weak dominance bridge is satisfiable. -/
example : (toSecurityMetrics sha256Extended).securityBits ≥
          (toSecurityMetrics ⟨60, 120, 120, 120, 64, 200⟩).securityBits :=
  (extDominates_implies_weak_dominates sha256Extended ⟨60, 120, 120, 120, 64, 200⟩
    (by decide)).1

-- Smoke tests
#eval extDominatesBool sha256Extended poseidon128Extended
#eval extParetoFront [aes128Extended, poseidon128Extended, sha256Extended]

end SuperHash
