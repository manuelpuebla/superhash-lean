/-!
# SuperHash.Concrete.GF2_4 — GF(2^4) Arithmetic (v4.5.4)

Finite field GF(2^4) = GF(16) represented as `Fin 16`.
Irreducible polynomial: x^4 + x + 1 (= 0b10011 = 19).

All field axioms verified by `native_decide` (16 x 16 = 256 cases).
Adapted from TrustHash BitVec4Arith pattern.
-/

namespace SuperHash.Concrete

/-- GF(2^4) element represented as Fin 16. -/
abbrev GF16 := Fin 16

/-! ## Basic Operations -/

/-- GF(2^4) zero element. -/
def gf16Zero : GF16 := ⟨0, by omega⟩

/-- GF(2^4) one element (multiplicative identity). -/
def gf16One : GF16 := ⟨1, by omega⟩

/-- XOR (addition in GF(2^4), characteristic 2). -/
def gf16Add (a b : GF16) : GF16 :=
  ⟨(a.val ^^^ b.val) % 16, by omega⟩

/-! ## Polynomial Multiplication mod x^4 + x + 1

Russian peasant method, unrolled for 4 bits.
Reduction: when bit 3 is set after shift, XOR with 0b0011 (= x+1,
the low bits of the irreducible polynomial x^4+x+1). -/

/-- Multiply by x in GF(2^4): left shift with reduction mod x^4+x+1. -/
private def gf16MulX (a : Nat) : Nat :=
  let shifted := (a <<< 1) &&& 0xF
  if a &&& 8 != 0 then shifted ^^^ 0b0011 else shifted

/-- GF(2^4) multiplication via shift-and-add, unrolled 4 steps. -/
def gf16Mul (a b : GF16) : GF16 :=
  let av := a.val
  let bv := b.val
  -- Step 0: bit 0 of b
  let r0 := if bv &&& 1 != 0 then av else 0
  let c0 := gf16MulX av
  -- Step 1: bit 1 of b
  let r1 := if bv &&& 2 != 0 then r0 ^^^ c0 else r0
  let c1 := gf16MulX c0
  -- Step 2: bit 2 of b
  let r2 := if bv &&& 4 != 0 then r1 ^^^ c1 else r1
  let c2 := gf16MulX c1
  -- Step 3: bit 3 of b
  let r3 := if bv &&& 8 != 0 then r2 ^^^ c2 else r2
  ⟨r3 % 16, by omega⟩

/-! ## Multiplicative Inverse (Lookup Table)

Precomputed: for each a in {1,...,15}, the unique b with a*b = 1 in GF(16).
Convention: inv(0) = 0. -/

def gf16InvNat (n : Nat) : Nat :=
  match n with
  | 0  => 0   -- convention (0 has no inverse)
  | 1  => 1   -- 1 * 1 = 1
  | 2  => 9   -- x * (x^3+1) = 1
  | 3  => 14  -- (x+1) * (x^3+x^2+x) = 1
  | 4  => 13
  | 5  => 11
  | 6  => 7
  | 7  => 6
  | 8  => 15
  | 9  => 2
  | 10 => 12
  | 11 => 5
  | 12 => 10
  | 13 => 4
  | 14 => 3
  | 15 => 8
  | _  => 0   -- unreachable for Fin 16

def gf16Inv (a : GF16) : GF16 :=
  ⟨gf16InvNat a.val % 16, by omega⟩

/-! ## Field Axioms

All axioms proved by `native_decide` over the finite domain (16 elements).
For Fin 16, this is an exhaustive check of all 16 or 16x16 cases. -/

/-- Additive commutativity: a + b = b + a. -/
theorem gf16Add_comm : ∀ (a b : GF16), gf16Add a b = gf16Add b a := by
  native_decide

/-- Additive associativity: (a + b) + c = a + (b + c). -/
theorem gf16Add_assoc : ∀ (a b c : GF16),
    gf16Add (gf16Add a b) c = gf16Add a (gf16Add b c) := by
  native_decide

/-- Additive identity: a + 0 = a. -/
theorem gf16Add_zero : ∀ (a : GF16), gf16Add a gf16Zero = a := by
  native_decide

/-- Additive self-inverse (characteristic 2): a + a = 0. -/
theorem gf16Add_self : ∀ (a : GF16), gf16Add a a = gf16Zero := by
  native_decide

/-- Multiplicative commutativity: a * b = b * a. -/
theorem gf16Mul_comm : ∀ (a b : GF16), gf16Mul a b = gf16Mul b a := by
  native_decide

/-- Multiplicative associativity: (a * b) * c = a * (b * c). -/
theorem gf16Mul_assoc : ∀ (a b c : GF16),
    gf16Mul (gf16Mul a b) c = gf16Mul a (gf16Mul b c) := by
  native_decide

/-- Multiplicative identity: a * 1 = a. -/
theorem gf16Mul_one : ∀ (a : GF16), gf16Mul a gf16One = a := by
  native_decide

/-- Distributivity: a * (b + c) = a*b + a*c. -/
theorem gf16Mul_distrib : ∀ (a b c : GF16),
    gf16Mul a (gf16Add b c) = gf16Add (gf16Mul a b) (gf16Mul a c) := by
  native_decide

/-- Multiplicative inverse: a != 0 -> a * inv(a) = 1. -/
theorem gf16Inv_correct : ∀ (a : GF16), a ≠ gf16Zero →
    gf16Mul a (gf16Inv a) = gf16One := by
  native_decide

/-! ## Additional Properties -/

/-- Zero annihilation (left): 0 * a = 0. -/
theorem gf16Mul_zero_left : ∀ (a : GF16), gf16Mul gf16Zero a = gf16Zero := by
  native_decide

/-- Zero annihilation (right): a * 0 = 0. -/
theorem gf16Mul_zero_right : ∀ (a : GF16), gf16Mul a gf16Zero = gf16Zero := by
  native_decide

/-- Inverse of zero is zero (convention). -/
theorem gf16Inv_zero : gf16Inv gf16Zero = gf16Zero := by native_decide

/-- Inverse of one is one. -/
theorem gf16Inv_one : gf16Inv gf16One = gf16One := by native_decide

/-- Double inverse: inv(inv(a)) = a. -/
theorem gf16Inv_inv : ∀ (a : GF16), gf16Inv (gf16Inv a) = a := by
  native_decide

/-- Inverse is unique: if a * b = 1 and a != 0, then b = inv(a). -/
theorem gf16Inv_unique : ∀ (a b : GF16),
    a ≠ gf16Zero → gf16Mul a b = gf16One → b = gf16Inv a := by
  native_decide

/-! ## Concrete Spot-Checks -/

/-- 2 * 9 = 1 (x * (x^3+1) = x^4+x = (x+1)+x = 1 mod p). -/
theorem gf16Mul_2_9 : gf16Mul ⟨2, by omega⟩ ⟨9, by omega⟩ = gf16One := by
  native_decide

/-- 3 * 14 = 1 ((x+1) * (x^3+x^2+x) = 1 mod p). -/
theorem gf16Mul_3_14 : gf16Mul ⟨3, by omega⟩ ⟨14, by omega⟩ = gf16One := by
  native_decide

/-- 5 * 11 = 1. -/
theorem gf16Mul_5_11 : gf16Mul ⟨5, by omega⟩ ⟨11, by omega⟩ = gf16One := by
  native_decide

-- Smoke tests
#eval gf16Mul ⟨3, by omega⟩ ⟨5, by omega⟩
#eval gf16Inv ⟨7, by omega⟩                   -- expected: 6
#eval gf16Mul ⟨7, by omega⟩ (gf16Inv ⟨7, by omega⟩)  -- expected: 1

end SuperHash.Concrete
