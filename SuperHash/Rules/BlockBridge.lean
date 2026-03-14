import SuperHash.Rules.CryptoRules

set_option linter.unusedSimpArgs false

/-!
# SuperHash.Rules.BlockBridge — Bridge theorems for hierarchical block constructors

v2.0: Four EquivalenceRule instances connecting block constructors to their
primitive compositions. Each bridge proves semantic equivalence under the
abstract Nat cost model.

Bridge theorems:
- spnBlock(r, s, l) ↔ iterate(r, compose(s, l))
- feistelBlock(r, f) ↔ iterate(r, f)
- spongeBlock(rt, cap, p) ↔ compose(iterate(rt, p), const(cap))
- arxBlock(r, a, rot, x) ↔ iterate(r, compose(compose(a, rot), x))
-/

namespace SuperHash

-- ============================================================
-- Bridge 1: spnBlock ↔ iterate(compose(sbox, linear))
-- ============================================================

/-- SPN block decomposes into iterated composition of S-box and linear layer.
    Semantics: r * (vs + vl) = r * (vs + vl). -/
def spnBlockBridgeRule : EquivalenceRule CryptoOp CryptoExpr Nat where
  name := "spnBlockBridge"
  rule := {
    name := "spnBlockBridge"
    lhs := .node (.spnBlock 0 0 0) [.patVar 0, .patVar 1]
    rhs := .node (.iterate 0 0) [.node (.compose 0 0) [.patVar 0, .patVar 1]]
  }
  lhsExpr := fun vars => .spnBlock ((vars 0).eval (fun _ => 0)) (vars 1) (vars 2)
  rhsExpr := fun vars => .iterate ((vars 0).eval (fun _ => 0))
                                   (.compose (vars 1) (vars 2))
  eval := cryptoEval
  soundness := by
    intro env vars
    simp [cryptoEval, CryptoExpr.eval]

-- ============================================================
-- Bridge 2: feistelBlock ↔ iterate(f)
-- ============================================================

/-- Feistel block decomposes into iterated round function.
    Semantics: r * vf = r * vf. -/
def feistelBlockBridgeRule : EquivalenceRule CryptoOp CryptoExpr Nat where
  name := "feistelBlockBridge"
  rule := {
    name := "feistelBlockBridge"
    lhs := .node (.feistelBlock 0 0) [.patVar 0]
    rhs := .node (.iterate 0 0) [.patVar 0]
  }
  lhsExpr := fun vars => .feistelBlock ((vars 0).eval (fun _ => 0)) (vars 1)
  rhsExpr := fun vars => .iterate ((vars 0).eval (fun _ => 0)) (vars 1)
  eval := cryptoEval
  soundness := by
    intro env vars
    simp [cryptoEval, CryptoExpr.eval]

-- ============================================================
-- Bridge 3: spongeBlock ↔ compose(iterate(perm), const(cap))
-- ============================================================

/-- Sponge block decomposes into iterated permutation composed with capacity constant.
    Semantics: rt * vp + cap = (rt * vp) + cap. -/
def spongeBlockBridgeRule : EquivalenceRule CryptoOp CryptoExpr Nat where
  name := "spongeBlockBridge"
  rule := {
    name := "spongeBlockBridge"
    lhs := .node (.spongeBlock 0 0 0) [.patVar 0]
    rhs := .node (.compose 0 0) [.node (.iterate 0 0) [.patVar 0], .node (.const 0) []]
  }
  lhsExpr := fun vars => .spongeBlock ((vars 0).eval (fun _ => 0))
                                       ((vars 1).eval (fun _ => 0)) (vars 2)
  rhsExpr := fun vars => .compose
    (.iterate ((vars 0).eval (fun _ => 0)) (vars 2))
    (.const ((vars 1).eval (fun _ => 0)))
  eval := cryptoEval
  soundness := by
    intro env vars
    simp [cryptoEval, CryptoExpr.eval]

-- ============================================================
-- Bridge 4: arxBlock ↔ iterate(compose(compose(add, rotate), xor))
-- ============================================================

/-- ARX block decomposes into iterated triple composition.
    Semantics: r * (va + vrot + vx) = r * ((va + vrot) + vx).
    Uses Nat.add_assoc for the associativity. -/
def arxBlockBridgeRule : EquivalenceRule CryptoOp CryptoExpr Nat where
  name := "arxBlockBridge"
  rule := {
    name := "arxBlockBridge"
    lhs := .node (.arxBlock 0 0 0 0) [.patVar 0, .patVar 1, .patVar 2]
    rhs := .node (.iterate 0 0)
      [.node (.compose 0 0)
        [.node (.compose 0 0) [.patVar 0, .patVar 1], .patVar 2]]
  }
  lhsExpr := fun vars => .arxBlock ((vars 0).eval (fun _ => 0))
                                     (vars 1) (vars 2) (vars 3)
  rhsExpr := fun vars => .iterate ((vars 0).eval (fun _ => 0))
    (.compose (.compose (vars 1) (vars 2)) (vars 3))
  eval := cryptoEval
  soundness := by
    intro env vars
    simp [cryptoEval, CryptoExpr.eval, Nat.add_assoc]

-- ============================================================
-- Non-vacuity examples
-- ============================================================

/-- spnBlockBridge is non-vacuous: concrete SPN (10 rounds, sbox-7, linear-5). -/
example : cryptoEval (.spnBlock 10 (.const 7) (.const 5)) (fun _ => 0) =
          cryptoEval (.iterate 10 (.compose (.const 7) (.const 5))) (fun _ => 0) := by
  simp [cryptoEval, CryptoExpr.eval]

/-- feistelBlockBridge is non-vacuous: Feistel (16 rounds, round function value 3). -/
example : cryptoEval (.feistelBlock 16 (.const 3)) (fun _ => 0) =
          cryptoEval (.iterate 16 (.const 3)) (fun _ => 0) := by
  simp [cryptoEval, CryptoExpr.eval]

/-- spongeBlockBridge is non-vacuous: Sponge (8 rate, 4 capacity, perm value 5). -/
example : cryptoEval (.spongeBlock 8 4 (.const 5)) (fun _ => 0) =
          cryptoEval (.compose (.iterate 8 (.const 5)) (.const 4)) (fun _ => 0) := by
  simp [cryptoEval, CryptoExpr.eval]

/-- arxBlockBridge is non-vacuous: ARX (20 rounds, add=2, rot=3, xor=1). -/
example : cryptoEval (.arxBlock 20 (.const 2) (.const 3) (.const 1)) (fun _ => 0) =
          cryptoEval (.iterate 20 (.compose (.compose (.const 2) (.const 3)) (.const 1))) (fun _ => 0) := by
  simp [cryptoEval, CryptoExpr.eval, Nat.add_assoc]

-- ============================================================
-- Collected bridge rules
-- ============================================================

/-- All four block bridge rules collected for pipeline use. -/
def blockBridgeRules : List (EquivalenceRule CryptoOp CryptoExpr Nat) :=
  [spnBlockBridgeRule, feistelBlockBridgeRule, spongeBlockBridgeRule, arxBlockBridgeRule]

end SuperHash
