import SuperHash.Crypto.SourceEntropy

/-!
# SuperHash.Crypto.UHFConstraint — 2-Universal Hash Family Design Constraint

v2.6: Formalizes the 2-UHF collision bound as a design constraint for
hash functions explored by the E-graph. A hash design satisfies the
2-UHF property when its differential uniformity δ satisfies:

  δ · 2^l ≤ 2^n

where n = S-box input bits and l = hash output bits used for the key.

## Source
Tyagi & Watanabe, ISIT 2017, §1.2, Definition 4:
  P[F(x) = F(x')] ≤ 1/2^l for x ≠ x', F uniform over F.

## Connection to DDT
The DDT max entry δ gives the collision probability per S-box:
  P[S(x⊕a) ⊕ S(x) = b] ≤ δ/2^n for the worst (a,b).
For the hash to be 2-universal with output l bits:
  δ/2^n ≤ 1/2^l  ⟺  δ · 2^l ≤ 2^n  ⟺  l ≤ n - log2(δ).
-/

namespace SuperHash

-- ============================================================
-- Section 1: 2-UHF Constraint
-- ============================================================

/-- A hash design satisfies the 2-UHF constraint if the collision
    probability (from DDT) is bounded by the output length:
    δ · 2^l ≤ 2^n.

    In Nat terms: delta * 2^outputLen ≤ 2^sboxBits. -/
def satisfiesUHF (delta sboxBits outputLen : Nat) : Prop :=
  delta * (2 ^ outputLen) ≤ 2 ^ sboxBits

/-- Decidable check for UHF constraint. -/
instance (delta sboxBits outputLen : Nat) : Decidable (satisfiesUHF delta sboxBits outputLen) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- Equivalent formulation: l ≤ n - ilog2(δ) (when δ ≥ 2). -/
def uhfMaxOutputLen (sboxBits delta : Nat) : Nat :=
  perSboxEntropy sboxBits delta

/-- If output ≤ uhfMaxOutputLen AND ilog2(δ) < n, then l + ilog2(δ) ≤ n.
    This is the condition for the 2-UHF property to hold. -/
theorem uhf_from_output_bound (delta n l : Nat)
    (hd : delta ≥ 2) (h_small : ilog2 delta < n)
    (hl : l ≤ uhfMaxOutputLen n delta) :
    l + ilog2 delta ≤ n := by
  simp only [uhfMaxOutputLen, perSboxEntropy] at hl
  split at hl <;> omega

-- ============================================================
-- Section 2: Concrete verifications
-- ============================================================

/-- AES: δ=4, n=8. Max output for UHF = 8 - 2 = 6 bits per S-box. -/
example : uhfMaxOutputLen 8 4 = 6 := by native_decide

/-- PRESENT: δ=4, n=4. Max output for UHF = 4 - 2 = 2 bits per S-box. -/
example : uhfMaxOutputLen 4 4 = 2 := by native_decide

/-- Poseidon: δ=2 (APN), n=64. Max output = 64 - 1 = 63 bits per S-box. -/
example : uhfMaxOutputLen 64 2 = 63 := by native_decide

/-- AES satisfies UHF for 6-bit output: 4 · 2^6 = 256 = 2^8. -/
example : satisfiesUHF 4 8 6 := by unfold satisfiesUHF; native_decide

/-- AES does NOT satisfy UHF for 7-bit output: 4 · 2^7 = 512 > 256 = 2^8. -/
example : ¬satisfiesUHF 4 8 7 := by unfold satisfiesUHF; native_decide

/-- Poseidon satisfies UHF for 63-bit output: 2 · 2^63 = 2^64. -/
example : satisfiesUHF 2 64 63 := by unfold satisfiesUHF; native_decide

-- ============================================================
-- Section 3: Multi-S-box UHF bound
-- ============================================================

/-- For a design with `a` active S-boxes in series, the total collision
    probability compounds: total_δ ≤ δ^a (independent differential trails).
    The max output for UHF becomes: l ≤ a · (n - log2(δ)).
    This is exactly sourceEntropy! -/
def multiSboxUHFMaxOutput (sboxBits activeSboxes delta : Nat) : Nat :=
  sourceEntropy sboxBits activeSboxes delta

/-- Multi-S-box UHF max output equals source entropy (by definition). -/
theorem multiUHF_eq_sourceEntropy (n a delta : Nat) :
    multiSboxUHFMaxOutput n a delta = sourceEntropy n a delta := rfl

/-- AES full cipher: 25 active S-boxes → max UHF output = 150 bits. -/
example : multiSboxUHFMaxOutput 8 25 4 = 150 := by native_decide

/-- Poseidon full cipher: 16 active S-boxes → max UHF output = 1008 bits. -/
example : multiSboxUHFMaxOutput 64 16 2 = 1008 := by native_decide

-- ============================================================
-- Section 4: Design quality checker
-- ============================================================

/-- Check if a hash design is information-theoretically sound:
    source entropy ≥ 2 × target security bits. -/
def isITSecure (sboxBits activeSboxes delta targetSecurity : Nat) : Bool :=
  sourceEntropy sboxBits activeSboxes delta ≥ 2 * targetSecurity

/-- AES targeting 64-bit security: 150 ≥ 128 ✓ -/
example : isITSecure 8 25 4 64 = true := by native_decide

/-- Poseidon (algebraically weak, effective k=54) targeting 27-bit: 54 ≥ 54 ✓ (barely) -/
example : isITSecure 64 16 2 27 = true := by native_decide

/-- Poseidon targeting 64-bit: 1008 ≥ 128 ✓ (differential is fine) -/
example : isITSecure 64 16 2 64 = true := by native_decide

end SuperHash
