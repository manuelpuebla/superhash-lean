/-!
# SuperHash.CryptoOp — Crypto construction types and E-graph operations

Defines the cryptographic construction paradigm type and the node
operations used by the E-graph engine to explore the hash design space.

## CryptoConstruction
Four major families: SPN, Feistel, Sponge, ARX.

## CryptoOp
Eight constructors representing composable crypto building blocks.
Each child field is a `Nat` (E-class id) referencing another node
in the E-graph.
-/

namespace SuperHash

/-- Cryptographic construction paradigm.
    The four major families of symmetric-key constructions. -/
inductive CryptoConstruction where
  | SPN
  | Feistel
  | Sponge
  | ARX
  deriving Repr, DecidableEq, BEq, Hashable

/-- E-graph node operations for cryptographic hash design.
    Each constructor represents a composable building block.
    Convention: metadata parameters first, then E-class id children.
    v2.0 adds hierarchical block constructors (spnBlock, feistelBlock,
    spongeBlock, arxBlock) that decompose into primitives via bridge rules. -/
inductive CryptoOp where
  -- v1.0 primitives
  | sbox (degree : Nat) (child : Nat)
  | linear (branchNum : Nat) (child : Nat)
  | xor (left right : Nat)
  | round (degree : Nat) (bn : Nat) (child : Nat)
  | compose (first second : Nat)
  | parallel (left right : Nat)
  | iterate (n : Nat) (body : Nat)
  | const (val : Nat)
  -- v2.0 hierarchical blocks
  | spnBlock (rounds : Nat) (sboxChild linearChild : Nat)
  | feistelBlock (rounds : Nat) (fChild : Nat)
  | spongeBlock (rate capacity : Nat) (permChild : Nat)
  | arxBlock (rounds : Nat) (addChild rotChild xorChild : Nat)
  deriving Repr, DecidableEq, Hashable

/-- BEq via DecidableEq (ensures LawfulBEq compatibility). -/
instance : BEq CryptoOp where
  beq x y := decide (x = y)

instance : LawfulBEq CryptoOp where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true_eq.mpr rfl

instance : Inhabited CryptoOp where
  default := .const 0

instance : LawfulHashable CryptoOp where
  hash_eq {a b} h := by
    have := eq_of_beq h
    subst this; rfl

-- Smoke tests (v1.0)
#eval CryptoOp.sbox 7 0 == CryptoOp.sbox 7 0      -- true
#eval CryptoOp.sbox 7 0 == CryptoOp.sbox 3 0      -- false
#eval CryptoOp.const 42 == CryptoOp.const 42       -- true
#eval CryptoOp.xor 0 1 == CryptoOp.parallel 0 1   -- false

-- Smoke tests (v2.0 blocks)
#eval CryptoOp.spnBlock 10 0 1 == CryptoOp.spnBlock 10 0 1   -- true
#eval CryptoOp.spnBlock 10 0 1 == CryptoOp.spnBlock 8 0 1    -- false (diff rounds)
#eval CryptoOp.feistelBlock 16 0 == CryptoOp.feistelBlock 16 0 -- true
#eval CryptoOp.arxBlock 20 0 1 2 == CryptoOp.arxBlock 20 0 1 2 -- true

end SuperHash
