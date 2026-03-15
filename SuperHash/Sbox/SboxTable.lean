-- SuperHash/Sbox/SboxTable.lean
-- Concrete S-box representation as lookup tables
-- Foundation for DDT/LAT/AlgDegree computation
-- Adapted from TrustHash/Sbox/SboxTable.lean for Lean 4.28
-- Named SboxTable (not ConcreteSbox) to avoid collision with SuperHash.Crypto.DDT.ConcreteSbox

import SuperHash.Sbox.Bitwise

namespace SuperHash.Sbox

open SuperHash.Sbox.Bitwise

/-! ## SboxTable

An n-bit S-box represented as an `Array Nat` of size 2^n,
where `table[x]` gives S(x). All entries must be < 2^n. -/

/-- An n-bit S-box: lookup table of size 2^n with entries in [0, 2^n). -/
structure SboxTable where
  inputBits : Nat
  table : Array Nat
  h_size : table.size = 2 ^ inputBits
  h_range : ∀ i, (h : i < table.size) → table[i] < 2 ^ inputBits

/-- Evaluate the S-box at input x. Returns 0 for out-of-range inputs. -/
def SboxTable.eval (s : SboxTable) (x : Nat) : Nat :=
  if h : x < s.table.size then s.table[x]
  else 0

/-- S-box output is always in range for valid inputs. -/
theorem SboxTable.eval_lt (s : SboxTable) (x : Nat) (hx : x < 2 ^ s.inputBits) :
    s.eval x < 2 ^ s.inputBits := by
  unfold eval
  have hx' : x < s.table.size := s.h_size ▸ hx
  simp [hx']
  exact s.h_range x hx'

/-- Eval of out-of-range input returns 0. -/
theorem SboxTable.eval_oob (s : SboxTable) (x : Nat) (hx : x ≥ 2 ^ s.inputBits) :
    s.eval x = 0 := by
  unfold eval
  have : ¬(x < s.table.size) := by rw [s.h_size]; omega
  simp [this]

/-- The domain size of an n-bit S-box. -/
def SboxTable.domainSize (s : SboxTable) : Nat := 2 ^ s.inputBits

theorem SboxTable.domainSize_pos (s : SboxTable) : s.domainSize > 0 := by
  unfold domainSize; exact Nat.two_pow_pos s.inputBits

theorem SboxTable.table_size_eq_domain (s : SboxTable) :
    s.table.size = s.domainSize := s.h_size

/-! ## S-box XOR differential

Core operation for DDT: S(x XOR a) XOR S(x) for input difference a.
Both x and a are taken mod 2^n to stay in domain. -/

/-- Output difference: S(x XOR a mod 2^n) XOR S(x mod 2^n). -/
def SboxTable.outputDiff (s : SboxTable) (x a : Nat) : Nat :=
  let n := s.inputBits
  let xmod := x % (2 ^ n)
  let xa := (xorNat xmod a) % (2 ^ n)
  xorNat (s.eval xa) (s.eval xmod)

/-! ## Concrete S-box instances -/

/-- PRESENT 4-bit S-box (Bogdanov et al. 2007).
    Known properties: delta = 4, NL = 4, deg = 3. -/
def presentSbox : SboxTable where
  inputBits := 4
  table := #[12, 5, 6, 11, 9, 0, 10, 13, 3, 14, 15, 8, 4, 7, 1, 2]
  h_size := by native_decide
  h_range := by
    intro i hi
    simp at hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
           i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
    rcases this with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp <;> omega

/-- Toy 2-bit S-box for fast testing: [1, 0, 3, 2] (swap pairs). -/
def toy2Sbox : SboxTable where
  inputBits := 2
  table := #[1, 0, 3, 2]
  h_size := by native_decide
  h_range := by
    intro i hi
    simp at hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases this with h|h|h|h <;> subst h <;> simp <;> omega

/-- Toy 3-bit S-box: [1, 2, 3, 4, 5, 6, 7, 0] (cyclic shift). -/
def toy3Sbox : SboxTable where
  inputBits := 3
  table := #[1, 2, 3, 4, 5, 6, 7, 0]
  h_size := by native_decide
  h_range := by
    intro i hi
    simp at hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases this with h|h|h|h|h|h|h|h <;> subst h <;> simp <;> omega

/-! ## Verification tests -/

theorem presentSbox_inputBits : presentSbox.inputBits = 4 := rfl

theorem presentSbox_domainSize : presentSbox.domainSize = 16 := by native_decide

theorem presentSbox_eval_0 : presentSbox.eval 0 = 12 := by native_decide

theorem presentSbox_eval_5 : presentSbox.eval 5 = 0 := by native_decide

theorem toy2Sbox_eval_0 : toy2Sbox.eval 0 = 1 := by native_decide

theorem toy2Sbox_eval_3 : toy2Sbox.eval 3 = 2 := by native_decide

/-- PRESENT S-box output diff test: S(0 XOR 1) XOR S(0) = S(1) XOR S(0) = 5 XOR 12. -/
theorem presentSbox_diff_0_1 : presentSbox.outputDiff 0 1 = 9 := by native_decide

end SuperHash.Sbox
