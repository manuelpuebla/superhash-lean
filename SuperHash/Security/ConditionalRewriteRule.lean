import SuperHash.Security.AlgExpr
/-!
# SuperHash.Security.ConditionalRewriteRule — Conditional sound rewrite rules

## Scope
Extends algebraic rewrite rules with decidable side conditions.
A `ConditionalRewriteRule` fires only when both:
1. The structural pattern matches (apply returns `some`)
2. The side condition holds (`sideCond` returns `true`)

This captures cryptanalytic rewrite rules that are sound only under
specific conditions (e.g., differential rules valid only when active
S-box count exceeds a threshold, or linear rules valid only when
bias exceeds a minimum).

## Key Results
- `ConditionalRewriteRule` — structure with decidable side condition
- `RewriteRule` — unconditional (always-true side condition) base
- `toConditional` — embedding of unconditional rules
- `conditionalApply_sound` — soundness of conditional application
- `conditionalChainSound` — chaining preserves evaluation semantics

## References
- Adapted from TrustHash.ConditionalRewriteRule (Lean 4.16.0 → 4.28.0)
- OptiSat.SoundRule.ConditionalSoundRewriteRule (simplified for AlgExpr/eval)
-/

namespace SuperHash.Security.ConditionalRewriteRule

open SuperHash.Security.AlgExpr (AlgExpr Env eval)

-- ============================================================
-- Section 1: Unconditional RewriteRule (base)
-- ============================================================

/-- **Sound rewrite rule (unconditional).**
    A rewrite rule that preserves evaluation semantics whenever it fires.
    This is the base type; ConditionalRewriteRule adds a side condition. -/
structure RewriteRule where
  /-- Human-readable name for the rule. -/
  name : String
  /-- Apply the structural rewrite (returns None if pattern doesn't match). -/
  apply : AlgExpr → Option AlgExpr
  /-- Soundness: when the rule fires, evaluation is preserved. -/
  sound : ∀ (e e' : AlgExpr) (env : Env),
    apply e = some e' → eval e env = eval e' env

/-- **Apply a rewrite rule, returning the original on no-match.** -/
def applyRuleOrId (r : RewriteRule) (e : AlgExpr) : AlgExpr :=
  (r.apply e).getD e

/-- **applyRuleOrId preserves evaluation.** -/
theorem applyRuleOrId_sound (r : RewriteRule) (e : AlgExpr) (env : Env) :
    eval (applyRuleOrId r e) env = eval e env := by
  unfold applyRuleOrId
  cases h : r.apply e with
  | none => simp [Option.getD]
  | some e' =>
    simp [Option.getD]
    exact (r.sound e e' env h).symm

/-- **Apply a chain of unconditional rules sequentially.** -/
def applyChain (rules : List RewriteRule) (e : AlgExpr) : AlgExpr :=
  rules.foldl (fun acc rule => applyRuleOrId rule acc) e

/-- **Chaining unconditional rules preserves evaluation.** -/
theorem chainSound (rules : List RewriteRule) (e : AlgExpr) (env : Env) :
    eval (applyChain rules e) env = eval e env := by
  unfold applyChain
  induction rules generalizing e with
  | nil => simp [List.foldl]
  | cons rule rest ih =>
    simp only [List.foldl]
    rw [ih (applyRuleOrId rule e), applyRuleOrId_sound]

-- ============================================================
-- Section 2: ConditionalRewriteRule Structure
-- ============================================================

/-- **Conditional sound rewrite rule**: a rewrite rule with a decidable
    side condition on the source expression.

    Examples of side conditions:
    - differential attack rules that only apply when active S-box count > threshold
    - linear attack rules that only apply when bias exceeds a minimum
    - algebraic attack rules that only apply when degree < bound

    The side condition is `AlgExpr → Bool` (decidable by construction). -/
structure ConditionalRewriteRule where
  /-- Human-readable name for the rule. -/
  name : String
  /-- Apply the structural rewrite (returns None if pattern doesn't match). -/
  apply : AlgExpr → Option AlgExpr
  /-- Side condition that must hold for the rule to fire. -/
  sideCond : AlgExpr → Bool
  /-- Soundness: when the rule fires AND side condition holds,
      evaluation is preserved. -/
  sound : ∀ (e e' : AlgExpr) (env : Env),
    sideCond e = true → apply e = some e' → eval e env = eval e' env

-- ============================================================
-- Section 3: Embedding of Unconditional Rules
-- ============================================================

/-- **Embed an unconditional RewriteRule as a ConditionalRewriteRule**
    with trivially true side condition. -/
def toConditional (r : RewriteRule) : ConditionalRewriteRule where
  name := r.name
  apply := r.apply
  sideCond := fun _ => true
  sound := fun e e' env _htrue h => r.sound e e' env h

/-- The embedding preserves apply behavior: when sideCond is trivially true,
    the conditional rule fires exactly when the unconditional one does. -/
theorem toConditional_equiv (r : RewriteRule) (e : AlgExpr) :
    (toConditional r).apply e = r.apply e := rfl

/-- The side condition of an embedded rule is always true. -/
theorem toConditional_sideCond (r : RewriteRule) (e : AlgExpr) :
    (toConditional r).sideCond e = true := rfl

-- ============================================================
-- Section 4: Conditional Apply and Soundness
-- ============================================================

/-- **Apply a conditional rule**: fires only when side condition holds.
    Returns the original expression if:
    - pattern doesn't match, OR
    - side condition is false -/
def conditionalApply (rule : ConditionalRewriteRule) (e : AlgExpr) : AlgExpr :=
  if rule.sideCond e then
    (rule.apply e).getD e
  else
    e

/-- **Conditional apply preserves evaluation.** -/
theorem conditionalApply_sound (rule : ConditionalRewriteRule)
    (e : AlgExpr) (env : Env) :
    eval (conditionalApply rule e) env = eval e env := by
  unfold conditionalApply
  split
  case isTrue hc =>
    cases h : rule.apply e with
    | none => simp [Option.getD]
    | some e' =>
      simp [Option.getD]
      exact (rule.sound e e' env hc h).symm
  case isFalse _ => rfl

-- ============================================================
-- Section 5: Conditional Chaining
-- ============================================================

/-- **Apply a chain of conditional rules sequentially.** -/
def conditionalChain (rules : List ConditionalRewriteRule) (e : AlgExpr) : AlgExpr :=
  rules.foldl (fun acc rule => conditionalApply rule acc) e

/-- **Chaining conditional rules preserves evaluation.** -/
theorem conditionalChainSound (rules : List ConditionalRewriteRule)
    (e : AlgExpr) (env : Env) :
    eval (conditionalChain rules e) env = eval e env := by
  unfold conditionalChain
  induction rules generalizing e with
  | nil => simp [List.foldl]
  | cons rule rest ih =>
    simp only [List.foldl]
    rw [ih (conditionalApply rule e), conditionalApply_sound]

-- ============================================================
-- Section 6: Backward Compatibility
-- ============================================================

/-- **Convert a list of unconditional rules to conditional rules.** -/
def liftRules (rules : List RewriteRule) : List ConditionalRewriteRule :=
  rules.map toConditional

/-- **Applying an embedded unconditional rule via conditionalApply is
    the same as applying it via applyRuleOrId.** -/
theorem toConditional_apply_eq (r : RewriteRule) (e : AlgExpr) :
    conditionalApply (toConditional r) e = applyRuleOrId r e := by
  unfold conditionalApply toConditional applyRuleOrId
  simp

/-- **Backward compatibility: chaining lifted rules produces the
    same result as the original unconditional chain.** -/
theorem backward_compat (rules : List RewriteRule) (e : AlgExpr) :
    conditionalChain (liftRules rules) e = applyChain rules e := by
  unfold conditionalChain liftRules applyChain
  induction rules generalizing e with
  | nil => simp [List.foldl]
  | cons r rest ih =>
    simp only [List.map, List.foldl]
    rw [toConditional_apply_eq]
    exact ih (applyRuleOrId r e)

-- ============================================================
-- Section 7: Mixed Chaining (Unconditional + Conditional)
-- ============================================================

/-- **Apply a mixed chain: first unconditional, then conditional rules.** -/
def mixedChain (unconditional : List RewriteRule)
    (conditional : List ConditionalRewriteRule) (e : AlgExpr) : AlgExpr :=
  conditionalChain conditional (applyChain unconditional e)

/-- **Mixed chain preserves evaluation.** -/
theorem mixedChainSound (unconditional : List RewriteRule)
    (conditional : List ConditionalRewriteRule) (e : AlgExpr) (env : Env) :
    eval (mixedChain unconditional conditional e) env = eval e env := by
  unfold mixedChain
  rw [conditionalChainSound, chainSound]

-- ============================================================
-- Section 8: Rule Count
-- ============================================================

/-- Total number of rules in a mixed chain. -/
def mixedRuleCount (unconditional : List RewriteRule)
    (conditional : List ConditionalRewriteRule) : Nat :=
  unconditional.length + conditional.length

/-- Lifted rules preserve length. -/
theorem liftRules_length (rules : List RewriteRule) :
    (liftRules rules).length = rules.length := by
  unfold liftRules; simp [List.length_map]

-- ============================================================
-- Section 9: Connection to CryptoOp (documentation)
-- ============================================================

/-! ### Intended bridge to CryptoOp

`AlgExpr` and `ConditionalRewriteRule` operate over a generic algebraic
expression AST with 5 constructors (const, var, add, mul, pow). The
SuperHash E-graph uses `CryptoOp` with 12 constructors (sbox, linear,
xor, round, compose, parallel, iterate, const, spnBlock, feistelBlock,
spongeBlock, arxBlock).

**Why no `cryptoOpToAlgExpr` function exists here**: the mapping from
CryptoOp to AlgExpr is domain-specific and lossy. CryptoOp encodes
structural composition (compose, parallel, iterate) and cryptographic
primitives (sbox, linear, round, etc.) that have no natural algebraic
analog. The meaningful connection is:

1. **Algebraic degree**: CryptoOp's `sbox d child` has algebraic degree
   `d`, which maps to `AlgExpr.pow (AlgExpr.var 0) d`. This is used by
   `SecurityNotions.algebraicBitsOf` (via `ilog2(cs.algebraicDegree)`).

2. **Round composition**: `iterate n (sbox d _)` has total algebraic
   degree `d^n`, which maps to `AlgExpr.pow (AlgExpr.var 0) (d^n)`.

3. **Conditional rules**: the `sideCond` field of `ConditionalRewriteRule`
   is designed for conditions like "active S-box count > threshold" or
   "algebraic degree < bound", which are computed from CryptoSemantics
   fields (not from AlgExpr structure).

The connection is INDIRECT: CryptoOp -> CryptoSemantics (via evalCryptoOpSem)
-> SecurityProfile (via cryptoSemanticsToProfile) -> security bits that
can be expressed as AlgExpr for simplification/verification.

A direct `cryptoOpToAlgExpr` would require choosing a single AlgExpr
representation for multi-dimensional CryptoOp nodes (e.g., sbox has both
algebraic degree AND differential uniformity), which would lose information.
The current architecture keeps these concerns separate:
- CryptoOp + CryptoSemantics: full multi-dimensional crypto analysis
- AlgExpr + ConditionalRewriteRule: algebraic simplification/verification
-/

end SuperHash.Security.ConditionalRewriteRule
