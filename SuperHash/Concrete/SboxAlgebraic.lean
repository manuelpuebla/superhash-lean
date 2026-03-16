import SuperHash.Concrete.GF2_4
import SuperHash.Sbox.SboxTable

/-!
# SuperHash.Concrete.SboxAlgebraic — S-box algebraic verification over GF(2^4) (v4.5.4)

Connects GF(2^4) field arithmetic to S-box table evaluation.
Enables algebraic property verification via polynomial representation.
-/

namespace SuperHash.Concrete

open SuperHash.Concrete

/-- Raise a GF(2^4) element to a natural number power. -/
def gf16Pow (base : GF16) : Nat → GF16
  | 0 => gf16One
  | n + 1 => gf16Mul base (gf16Pow base n)

/-- Evaluate a polynomial over GF(2^4) at a point.
    Coefficients are in ascending degree order: c₀ + c₁x + c₂x² + ...
    Uses `zipIdx` to pair each coefficient with its index. -/
def evalPoly (coeffs : List GF16) (x : GF16) : GF16 :=
  coeffs.zipIdx.foldl (fun acc (c, i) =>
    gf16Add acc (gf16Mul c (gf16Pow x i))
  ) gf16Zero

/-- Verify that a lookup table matches polynomial evaluation over GF(2^4).
    Returns true if table[i] = poly(i) for all i ∈ 0..15. -/
def verifyPoly (table : Array Nat) (coeffs : List GF16) : Bool :=
  (List.range 16).all fun i =>
    let h : i % 16 < 16 := Nat.mod_lt i (by omega)
    table.getD i 0 == (evalPoly coeffs ⟨i % 16, h⟩).val

/-- Algebraic degree of a polynomial (index of highest nonzero coefficient). -/
def polyDegree (coeffs : List GF16) : Nat :=
  match coeffs.reverse.dropWhile (· == gf16Zero) with
  | [] => 0
  | _ :: rest => rest.length

-- Properties
theorem polyDegree_const : ∀ (c : GF16), polyDegree [c] = 0 := by native_decide

/-- The inversion map x → x^{-1} in GF(2^4) as a lookup table.
    Convention: inv(0) = 0 (matches gf16Inv). -/
def gf16InvTable : Array Nat :=
  #[0, 1, 9, 14, 13, 11, 7, 6, 15, 2, 12, 5, 10, 4, 3, 8]

/-- Verify inversion table matches gf16Inv for all inputs. -/
theorem gf16InvTable_correct :
    ∀ i : Fin 16, gf16InvTable.getD i.val 0 = (gf16Inv ⟨i.val, i.isLt⟩).val := by
  native_decide

/-- Verify inversion table is self-inverse: inv(inv(x)) = x for all x ≠ 0. -/
theorem gf16InvTable_involutive :
    ∀ i : Fin 16, i.val ≠ 0 →
      gf16InvTable.getD (gf16InvTable.getD i.val 0) 0 = i.val := by
  native_decide

/-- gf16Pow computes x^0 = 1. -/
theorem gf16Pow_zero (x : GF16) : gf16Pow x 0 = gf16One := rfl

/-- gf16Pow computes x^1 = x. -/
theorem gf16Pow_one : ∀ (x : GF16), gf16Pow x 1 = x := by native_decide

/-- Constant polynomial evaluates to its coefficient. -/
theorem evalPoly_const : ∀ (c x : GF16), evalPoly [c] x = c := by native_decide

-- Smoke tests
#eval evalPoly [⟨1, by omega⟩, ⟨0, by omega⟩, ⟨1, by omega⟩] ⟨3, by omega⟩
#eval polyDegree [⟨1, by omega⟩, ⟨0, by omega⟩, ⟨1, by omega⟩]  -- degree 2
#eval gf16InvTable  -- [0, 1, 9, 14, ...]
#eval gf16Pow ⟨2, by omega⟩ 4  -- 2^4 in GF(16) = x^4 = x+1 = 3
-- Verify that verifyPoly returns true for identity polynomial p(x) = x over GF(2^4)
#eval verifyPoly #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  [⟨0, by omega⟩, ⟨1, by omega⟩]  -- true: p(i) = 0 + 1*i = i

end SuperHash.Concrete
