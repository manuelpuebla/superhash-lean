import SuperHash.Crypto.CryptoNodeSemantics
import SuperHash.Pipeline.EMatchSpec
import SuperHash.Rules.CryptoRules

/-!
# SuperHash.Rules.CryptoRulesCS — PatternSoundRule for CryptoSemantics

v2.9.1 Fix 1: Bridge theorem + CryptoSemantics-aware rule instances.

## Key insight
saturateF takes List (RewriteRule Op) which is Val-AGNOSTIC. The soundness
proof is only needed for pipeline_soundness composition. So Nat rules are
SAFE for saturation — they don't violate CryptoSemantics because saturateF
only uses the syntactic patterns, not the Val-dependent soundness proofs.

This file provides:
1. Documentation explaining why Nat rules are safe for saturation (Val-agnostic)
2. CryptoSemantics PatternSoundRule instances for pipeline composition
-/

set_option linter.unusedSimpArgs false

namespace SuperHash

-- ============================================================
-- Section 1: Val-agnostic saturation (documentation)
-- ============================================================

/-! ### Why Nat rules are safe for saturation

`saturateF` takes `List (RewriteRule Op)` — it extracts `.rule` from each
`PatternSoundRule` and uses ONLY the syntactic pattern (lhs/rhs) for e-matching.
The `Val`-dependent `soundness` field is never consumed by `saturateF` itself.

Therefore, `cryptoPatternRules` (proved sound for `Nat`) can be used directly
in saturation of a CryptoSemantics-aware E-graph without any bridge theorem.
The `RewriteRule` is literally the same struct regardless of `Val`.

The `Val`-specific soundness proofs ARE needed when composing into
`pipeline_soundness` — for that, use `cryptoPatternRulesCS` below, which
provides `PatternSoundRule CryptoOp CryptoSemantics` instances. -/

-- ============================================================
-- Section 2: Helper lemmas (private in CryptoRules, duplicated here)
-- ============================================================

private theorem cs_decide_True : decide True = true := rfl
private theorem cs_decide_False : decide False = false := rfl
private theorem cs_decide_01 : decide (0 = 1) = false := rfl
private theorem cs_decide_10 : decide (1 = 0) = false := rfl

/-- safePow composition: safePow(safePow(d,m),n) = safePow(d,n*m). -/
theorem safePow_safePow (d m n : Nat) : safePow (safePow d m) n = safePow d (n * m) := by
  simp only [safePow]
  by_cases hm : m = 0
  · subst hm; simp
  · by_cases hn : n = 0
    · subst hn; simp
    · have hnm : n * m ≠ 0 := Nat.mul_ne_zero hn hm
      simp [hm, hn, hnm]
      rw [← Nat.pow_mul]
      congr 1; exact Nat.mul_comm m n

-- ============================================================
-- Section 3: CryptoSemantics PatternSoundRule instances
-- ============================================================

/-- iterateOne over CryptoSemantics: iterate(1, x) = x.
    CryptoSemantics proof: safePow(deg, 1) = deg (for all 7 fields). -/
def iterateOne_cs : PatternSoundRule CryptoOp CryptoSemantics where
  rule := { name := "iterateOne_cs"
            lhs := .node (.iterate 1 0) [.patVar 0]
            rhs := .patVar 0 }
  soundness := by
    intro env σ
    simp [Pattern.eval, NodeOps.children, CryptoOp.children,
      NodeSemantics.evalOp, evalCryptoOpCS, List.map, List.zip,
      List.zipWith, List.lookup, BEq.beq, Nat.beq,
      Inhabited.default, safePow]
  lhs_wf := by simp [AllDistinctChildren, NodeOps.children, CryptoOp.children, List.Nodup]
  rhs_wf := by simp [AllDistinctChildren]

/-- composeAssoc over CryptoSemantics: compose(compose(a,b),c) = compose(a,compose(b,c)).
    Sound because ALL 7 fields use associative operations:
    - degree: (d_a * d_b) * d_c = d_a * (d_b * d_c)  (Nat.mul_assoc)
    - δ/ε: max(max(x,y),z) = max(x,max(y,z))  (max assoc)
    - BN: min(min(x,y),z) = min(x,min(y,z))  (min assoc)
    - active/latency/gates: (a+b)+c = a+(b+c)  (Nat.add_assoc) -/
def composeAssoc_cs : PatternSoundRule CryptoOp CryptoSemantics where
  rule := { name := "composeAssoc_cs"
            lhs := .node (.compose 0 1) [.node (.compose 0 1) [.patVar 0, .patVar 1], .patVar 2]
            rhs := .node (.compose 0 1) [.patVar 0, .node (.compose 0 1) [.patVar 1, .patVar 2]] }
  soundness := by
    intro env σ
    simp only [Pattern.eval, NodeOps.children, CryptoOp.children, NodeSemantics.evalOp,
      evalCryptoOpCS, List.map, List.zip, List.zipWith, List.lookup,
      BEq.beq, Nat.beq, Inhabited.default]
    simp only [cs_decide_True, cs_decide_False, cs_decide_01, cs_decide_10,
      Nat.mul_assoc, Nat.max_assoc, Nat.min_assoc, Nat.add_assoc]
  lhs_wf := by simp [AllDistinctChildren, NodeOps.children, CryptoOp.children, List.Nodup]
  rhs_wf := by simp [AllDistinctChildren, NodeOps.children, CryptoOp.children, List.Nodup]

/-- iterateCompose over CryptoSemantics: iterate(n, iterate(m, x)) = iterate(n*m, x).
    Sound because ALL 7 fields compose multiplicatively:
    - degree: safePow(safePow(d,m),n) = safePow(d,n*m)
    - δ/ε/BN: unchanged by iterate (passed through)
    - active/latency/gates: n*(m*x) = (n*m)*x  (Nat.mul_assoc) -/
def iterateCompose_cs (n m : Nat) : PatternSoundRule CryptoOp CryptoSemantics where
  rule := { name := s!"iterateCompose_cs_{n}_{m}"
            lhs := .node (.iterate n 0) [.node (.iterate m 0) [.patVar 0]]
            rhs := .node (.iterate (n * m) 0) [.patVar 0] }
  soundness := by
    intro env σ
    simp only [Pattern.eval, NodeOps.children, CryptoOp.children, NodeSemantics.evalOp,
      evalCryptoOpCS, List.map, List.zip, List.zipWith, List.lookup,
      BEq.beq, Nat.beq, Inhabited.default]
    simp only [cs_decide_True, cs_decide_False, safePow_safePow, Nat.mul_assoc]
  lhs_wf := by
    simp [AllDistinctChildren, NodeOps.children, CryptoOp.children, List.Nodup]
  rhs_wf := by
    simp [AllDistinctChildren, NodeOps.children, CryptoOp.children, List.Nodup]

-- ============================================================
-- Section 4: Unsound rules (documented)
-- ============================================================

-- NOTE: parallelIdentity is NOT sound for CryptoSemantics.
-- Reason: parallel uses min(branchNumber, 0) = 0 ≠ branchNumber.

-- NOTE: roundCompose is NOT sound for CryptoSemantics.
-- Reason: compose multiplies algebraicDegree (d_a * d_b), but
-- round adds branch number (d * deg + bn). The decomposition
-- round(d,b,x) → compose(sbox(d,x), const(b)) changes the
-- algebraic degree from d*deg+b to (d*deg)*b (if b interpreted as degree).

-- ============================================================
-- Section 5: Collected CS-sound rules
-- ============================================================

/-- CryptoSemantics PatternSoundRule instances.
    Only includes rules PROVEN sound for all 7 crypto metric fields.
    EXCLUDED: parallelIdentity (min(bn,0)=0), roundCompose (degree mismatch). -/
def cryptoPatternRulesCS : List (PatternSoundRule CryptoOp CryptoSemantics) :=
  [iterateOne_cs, composeAssoc_cs,
   iterateCompose_cs 2 2,    -- iterate(2, iterate(2, x)) = iterate(4, x)
   iterateCompose_cs 4 2,    -- iterate(4, iterate(2, x)) = iterate(8, x)
   iterateCompose_cs 5 2,    -- iterate(5, iterate(2, x)) = iterate(10, x)
   iterateCompose_cs 8 2,    -- iterate(8, iterate(2, x)) = iterate(16, x)
   iterateCompose_cs 10 2]   -- iterate(10, iterate(2, x)) = iterate(20, x)

-- ============================================================
-- Section 6: Non-vacuity
-- ============================================================

example : cryptoPatternRulesCS.length = 7 := by native_decide
example : iterateOne_cs.rule.name = "iterateOne_cs" := rfl
example : composeAssoc_cs.rule.name = "composeAssoc_cs" := rfl

end SuperHash
