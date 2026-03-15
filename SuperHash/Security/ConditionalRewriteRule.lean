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

end SuperHash.Security.ConditionalRewriteRule
