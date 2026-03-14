import SuperHash.CryptoNodeOps

/-!
# SuperHash.Concrete.BitVecOps — BitVec concrete semantics layer

v2.0 (N3.1): Concrete BitVec operations for S-box evaluation.
Uses Lean 4 core BitVec (no Mathlib dependency).

## Design (D9: Dual Semantic Layer)
- Abstract layer: Val:=Nat for metrics (v1.0 compatible)
- Concrete layer: BitVec n for bit-level operations
- Bridge theorem connects both (N3.2)

## BitVec in Lean 4 Core
- `BitVec n`: n-bit bitvector
- `bv_decide`: SAT-based decision procedure (CaDiCaL with LRAT certificate)
- `BitVec.xor`, `BitVec.and`, `BitVec.or`: bitwise ops
- `BitVec.toNat`, `BitVec.ofNat`: conversion to/from Nat
-/

namespace SuperHash

-- ============================================================
-- Core BitVec operations for crypto
-- ============================================================

/-- XOR two bitvectors (fundamental crypto operation). -/
def bvXor (a b : BitVec n) : BitVec n := a ^^^ b

/-- AND two bitvectors. -/
def bvAnd (a b : BitVec n) : BitVec n := a &&& b

/-- OR two bitvectors. -/
def bvOr (a b : BitVec n) : BitVec n := a ||| b

/-- NOT (complement) a bitvector. -/
def bvNot (a : BitVec n) : BitVec n := ~~~a

/-- Left rotate by k positions. -/
def bvRotateLeft (a : BitVec n) (k : Nat) : BitVec n := a.rotateLeft k

/-- Right rotate by k positions. -/
def bvRotateRight (a : BitVec n) (k : Nat) : BitVec n := a.rotateRight k

/-- Addition modulo 2^n (ARX primitive). -/
def bvAdd (a b : BitVec n) : BitVec n := a + b

-- ============================================================
-- S-box as lookup table
-- ============================================================

/-- An S-box is a lookup table mapping n-bit inputs to n-bit outputs. -/
structure Sbox (n : Nat) where
  /-- The lookup table: input → output -/
  table : Array (BitVec n)
  /-- Table has exactly 2^n entries -/
  h_size : table.size = 2 ^ n

/-- Apply an S-box to an input. -/
def Sbox.apply (sbox : Sbox n) (input : BitVec n) : BitVec n :=
  let idx := input.toNat
  if h : idx < sbox.table.size then
    sbox.table[idx]
  else
    input  -- fallback: identity (should not happen with valid Sbox)

-- ============================================================
-- BoundedInput predicate (D9, QA #3)
-- ============================================================

/-- A natural number x is bounded by n bits: x < 2^n.
    This is the formal precondition for abstract-concrete bridge theorems. -/
def BoundedInput (n : Nat) (x : Nat) : Prop := x < 2 ^ n

/-- 0 is always bounded (for n > 0). -/
theorem boundedInput_zero (n : Nat) (hn : 0 < n) : BoundedInput n 0 :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.one_le_pow n 2 (by omega))

/-- For 8-bit, any value < 256 is bounded. -/
example : BoundedInput 8 42 := by unfold BoundedInput; omega
example : BoundedInput 8 255 := by unfold BoundedInput; omega

-- ============================================================
-- Concrete evaluation of CryptoOp at BitVec level
-- ============================================================

/-- Evaluate a CryptoOp concretely using BitVec arithmetic.
    Maps abstract operations to concrete bit-level computations.
    The result is converted back to Nat for compatibility with the abstract layer. -/
def evalCryptoOpBitVec (n : Nat) : CryptoOp → List Nat → Nat
  | .xor _ _, [l, r] =>
    let bl := BitVec.ofNat n l
    let br := BitVec.ofNat n r
    (bvXor bl br).toNat
  | .const v, [] => v % (2 ^ n)  -- truncate to n bits
  | op, args => evalCryptoOp op args  -- fallback to abstract for non-bitwise ops

-- ============================================================
-- Basic BitVec properties (proven from first principles, no Mathlib)
-- ============================================================

/-- XOR is commutative. -/
theorem bvXor_comm (a b : BitVec n) : bvXor a b = bvXor b a := by
  simp [bvXor, BitVec.xor_comm]

/-- XOR is associative. -/
theorem bvXor_assoc (a b c : BitVec n) : bvXor (bvXor a b) c = bvXor a (bvXor b c) := by
  simp [bvXor, BitVec.xor_assoc]

/-- XOR with self is zero. -/
theorem bvXor_self (a : BitVec n) : bvXor a a = 0 := by
  simp [bvXor]

/-- XOR with zero is identity. -/
theorem bvXor_zero (a : BitVec n) : bvXor a 0 = a := by
  simp [bvXor]

/-- Addition is commutative. -/
theorem bvAdd_comm (a b : BitVec n) : bvAdd a b = bvAdd b a := by
  simp [bvAdd, BitVec.add_comm]

-- ============================================================
-- Smoke tests
-- ============================================================

#eval (bvXor (3 : BitVec 8) 5).toNat        -- 6 (011 XOR 101 = 110)
#eval (bvAdd (200 : BitVec 8) 100).toNat     -- 44 (300 mod 256)
#eval (bvRotateLeft (1 : BitVec 8) 3).toNat  -- 8 (00000001 → 00001000)
#eval (bvNot (0 : BitVec 8)).toNat           -- 255

-- BitVec concrete eval vs abstract eval
#eval evalCryptoOpBitVec 8 (.xor 0 1) [3, 5]  -- 6 (bitwise XOR)
#eval evalCryptoOp (.xor 0 1) [3, 5]           -- 8 (abstract: 3+5)

end SuperHash
