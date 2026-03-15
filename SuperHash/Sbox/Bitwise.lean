-- SuperHash/Sbox/Bitwise.lean
-- Bitwise operations for S-box analysis: XOR, popcount, parity over Nat
-- Foundation for DDT/LAT computation
-- Adapted from TrustHash/Bitwise.lean for Lean 4.28

namespace SuperHash.Sbox.Bitwise

/-! ## XOR on Nat

Lean 4.28 provides `Nat.xor` (operator `^^^`) with full lemma suite.
We re-export and add S-box-specific helpers. -/

/-- XOR of two Nat values, wrapping Nat.xor for clarity. -/
abbrev xorNat (a b : Nat) : Nat := a ^^^ b

theorem xorNat_comm (a b : Nat) : xorNat a b = xorNat b a :=
  Nat.xor_comm a b

theorem xorNat_assoc (a b c : Nat) : xorNat (xorNat a b) c = xorNat a (xorNat b c) :=
  Nat.xor_assoc a b c

theorem xorNat_self (a : Nat) : xorNat a a = 0 :=
  Nat.xor_self a

theorem xorNat_zero (a : Nat) : xorNat a 0 = a :=
  Nat.xor_zero a

theorem zero_xorNat (a : Nat) : xorNat 0 a = a :=
  Nat.zero_xor a

/-! ## Popcount (Hamming weight)

Count the number of 1-bits in a Nat value, checking bits 0..maxBit-1.
Used for parity computation in LAT. -/

/-- Tail-recursive popcount helper. Counts set bits in positions 0..n-1. -/
def popcountAux (x : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc =>
    let bit := if x.testBit n then 1 else 0
    popcountAux x n (acc + bit)

/-- Count bits set to 1 in positions 0..maxBit-1. -/
def popcount (x : Nat) (maxBit : Nat) : Nat :=
  popcountAux x maxBit 0

private theorem popcountAux_bound (x n acc : Nat) : popcountAux x n acc ≤ n + acc := by
  induction n generalizing acc with
  | zero => simp [popcountAux]
  | succ n ih =>
    simp [popcountAux]
    split
    · have := ih (acc + 1); omega
    · have := ih (acc + 0); omega

private theorem popcountAux_zero (n acc : Nat) : popcountAux 0 n acc = acc := by
  induction n generalizing acc with
  | zero => simp [popcountAux]
  | succ n ih => simp [popcountAux, Nat.zero_testBit]; exact ih acc

theorem popcount_zero (maxBit : Nat) : popcount 0 maxBit = 0 := by
  unfold popcount; exact popcountAux_zero maxBit 0

theorem popcount_le_maxBit (x maxBit : Nat) : popcount x maxBit ≤ maxBit := by
  unfold popcount; have := popcountAux_bound x maxBit 0; omega

/-! ## Parity

The parity of the Hamming weight, needed for LAT inner products.
parity(a AND x) = popcount(a AND x) mod 2. -/

/-- Parity of the bitwise AND of a and x over maxBit bits. -/
def innerParity (a x : Nat) (maxBit : Nat) : Nat :=
  popcount (Nat.land a x) maxBit % 2

theorem innerParity_le_one (a x maxBit : Nat) : innerParity a x maxBit ≤ 1 := by
  unfold innerParity; omega

/-- Inner product over GF(2): true if popcount(a AND x) is odd. -/
def dotF2 (a x : Nat) (n : Nat) : Bool :=
  innerParity a x n == 1

/-! ## Modular truncation

Truncate a Nat to n bits (mod 2^n). Needed for S-box operations. -/

/-- Truncate x to its lowest n bits. -/
def truncate (x : Nat) (n : Nat) : Nat := x % (2 ^ n)

theorem truncate_lt (x n : Nat) : truncate x n < 2 ^ n := by
  unfold truncate
  exact Nat.mod_lt x (Nat.two_pow_pos n)

theorem truncate_idempotent (x n : Nat) : truncate (truncate x n) n = truncate x n := by
  unfold truncate
  exact Nat.mod_eq_of_lt (Nat.mod_lt x (Nat.two_pow_pos n))

/-! ## XOR on truncated values

S-box XOR operates mod 2^n. -/

/-- XOR of two values truncated to n bits. -/
def xorMod (a b : Nat) (n : Nat) : Nat := truncate (xorNat a b) n

theorem xorMod_comm (a b n : Nat) : xorMod a b n = xorMod b a n := by
  unfold xorMod; rw [xorNat_comm]

theorem xorMod_lt (a b n : Nat) : xorMod a b n < 2 ^ n :=
  truncate_lt _ n

end SuperHash.Sbox.Bitwise
