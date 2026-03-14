import SuperHash.Rules.BlockBridge
import SuperHash.Rules.CryptoRules

/-!
# SuperHash.Rules.ExpansionRules — Bidirectional bridge rules for design exploration

v3.0: Creates REVERSE bridge rules (primitive → block) to enable bidirectional
exploration in the E-graph. With both simplification (block → primitive) and
expansion (primitive → block) rules, equality saturation discovers a RICHER
space of equivalent designs.

## Rules
- 4 reverse bridges: iterate∘compose → spnBlock, iterate → feistelBlock, etc.
- 1 roundSplit: iterate(2r, x) → compose(iterate(r,x), iterate(r,x))
- All use the SAME syntactic patterns as BlockBridge but swapped LHS↔RHS
-/

namespace SuperHash

-- ============================================================
-- Section 1: Reverse bridge rules (primitive → block)
-- ============================================================

/-- REVERSE spnBlock bridge: iterate(r, compose(s, l)) → spnBlock(r, s, l).
    Enables the E-graph to recognize composed primitives as SPN blocks. -/
def spnBlockReverseRule : RewriteRule CryptoOp where
  name := "spnBlockReverse"
  lhs := .node (.iterate 0 0) [.node (.compose 0 0) [.patVar 0, .patVar 1]]
  rhs := .node (.spnBlock 0 0 0) [.patVar 0, .patVar 1]

/-- REVERSE feistelBlock bridge: iterate(r, f) → feistelBlock(r, f). -/
def feistelBlockReverseRule : RewriteRule CryptoOp where
  name := "feistelBlockReverse"
  lhs := .node (.iterate 0 0) [.patVar 0]
  rhs := .node (.feistelBlock 0 0) [.patVar 0]

/-- REVERSE spongeBlock bridge: compose(iterate(rt, p), const(cap)) → spongeBlock(rt, cap, p). -/
def spongeBlockReverseRule : RewriteRule CryptoOp where
  name := "spongeBlockReverse"
  lhs := .node (.compose 0 0) [.node (.iterate 0 0) [.patVar 0], .node (.const 0) []]
  rhs := .node (.spongeBlock 0 0 0) [.patVar 0]

/-- REVERSE arxBlock bridge: iterate(r, compose(compose(a, rot), x)) → arxBlock(r, a, rot, x). -/
def arxBlockReverseRule : RewriteRule CryptoOp where
  name := "arxBlockReverse"
  lhs := .node (.iterate 0 0)
    [.node (.compose 0 0)
      [.node (.compose 0 0) [.patVar 0, .patVar 1], .patVar 2]]
  rhs := .node (.arxBlock 0 0 0 0) [.patVar 0, .patVar 1, .patVar 2]

-- ============================================================
-- Section 2: Forward bridge rules (extracted from BlockBridge)
-- ============================================================

/-- Forward bridge rules (block → primitive), extracted from EquivalenceRule instances. -/
def spnBlockForwardRule : RewriteRule CryptoOp :=
  spnBlockBridgeRule.rule
def feistelBlockForwardRule : RewriteRule CryptoOp :=
  feistelBlockBridgeRule.rule
def spongeBlockForwardRule : RewriteRule CryptoOp :=
  spongeBlockBridgeRule.rule
def arxBlockForwardRule : RewriteRule CryptoOp :=
  arxBlockBridgeRule.rule

-- ============================================================
-- Section 3: Round split rule (expansion)
-- ============================================================

/-- Round split: iterate(n, x) → compose(iterate(n/2, x), iterate(n - n/2, x)).
    This is an EXPANSION rule: splits a multi-round design into two halves,
    enabling the E-graph to explore partial optimizations on each half.

    For n=10: iterate(10, x) → compose(iterate(5, x), iterate(5, x))
    Each half can then be independently optimized by other rules. -/
def roundSplitRule (n : Nat) (hn : n ≥ 2) : RewriteRule CryptoOp where
  name := s!"roundSplit_{n}"
  lhs := .node (.iterate n 0) [.patVar 0]
  rhs := .node (.compose 0 0)
    [.node (.iterate (n / 2) 0) [.patVar 0],
     .node (.iterate (n - n / 2) 0) [.patVar 0]]

-- ============================================================
-- Section 4: Collected expansion rules
-- ============================================================

/-- ALL expansion + bridge rules for design space exploration.
    Combined with cryptoPatternRules (simplification), these enable
    bidirectional equality saturation. -/
def expansionRules : List (RewriteRule CryptoOp) :=
  [ -- Forward bridges (block → primitive)
    spnBlockForwardRule, feistelBlockForwardRule,
    spongeBlockForwardRule, arxBlockForwardRule,
    -- Reverse bridges (primitive → block)
    spnBlockReverseRule, feistelBlockReverseRule,
    spongeBlockReverseRule, arxBlockReverseRule,
    -- Round split (expansion)
    roundSplitRule 10 (by omega),  -- AES: 10 → 5+5
    roundSplitRule 8 (by omega)    -- Poseidon: 8 → 4+4
  ]

-- ============================================================
-- Section 5: Non-vacuity
-- ============================================================

#eval expansionRules.length  -- 10

example : expansionRules.length = 10 := by native_decide

end SuperHash
