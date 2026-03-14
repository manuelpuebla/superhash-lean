import SuperHash.Discovery.RuleVerifier
import SuperHash.Pipeline.Saturate

/-!
# SuperHash.Discovery.RulePool — Dynamic verified rule pool

v2.0: A `RulePool` is a collection of `VerifiedRule` instances that can grow
dynamically as new rules are discovered and verified. The pool maintains the
invariant that ALL rules are kernel-verified (rulePool_all_equivalent).

## Key Properties
- `rulePool_all_equivalent`: every rule in the pool has a soundness proof
- `addRule`: only accepts VerifiedRule (proof required at call site)
- `toRewriteRules`: converts pool to RewriteRule list for saturateF
-/

namespace SuperHash

-- ============================================================
-- Rule pool structure
-- ============================================================

/-- A pool of verified rewrite rules.
    Invariant: every rule in `rules` has been kernel-verified. -/
structure RulePool where
  /-- Collection of verified rules -/
  rules : List VerifiedRule
  deriving Inhabited

/-- Empty rule pool. -/
def RulePool.empty : RulePool := ⟨[]⟩

/-- Number of rules in the pool. -/
def RulePool.size (pool : RulePool) : Nat := pool.rules.length

/-- Add a verified rule to the pool. -/
def RulePool.addRule (pool : RulePool) (vr : VerifiedRule) : RulePool :=
  ⟨vr :: pool.rules⟩

/-- Remove rules by name. -/
def RulePool.removeByName (pool : RulePool) (name : String) : RulePool :=
  ⟨pool.rules.filter (·.candidate.name != name)⟩

/-- Score a rule based on its classification and confidence. -/
def RulePool.scoreRule (_pool : RulePool) (vr : VerifiedRule) : Nat :=
  let classBonus := match vr.candidate.classification with
    | .equivalence => 3  -- equivalence rules are most valuable
    | .improvement => 2
    | .conditional => 1
  classBonus * vr.candidate.confidence

-- ============================================================
-- Pool invariant: all rules are sound
-- ============================================================

/-- Pool invariant: every rule's LHS and RHS templates evaluate identically.
    NOTE: This proves template EQUIVALENCE, not crypto soundness.
    Crypto soundness (security preservation) requires additional domain-specific proofs. -/
theorem rulePool_all_equivalent (pool : RulePool) :
    ∀ vr ∈ pool.rules, ∀ env : Nat → Nat,
      vr.candidate.lhsTemplate.eval env = vr.candidate.rhsTemplate.eval env :=
  fun vr hvr env => vr.sound env

/-- Adding a verified rule preserves the pool invariant. -/
theorem addRule_preserves_sound (pool : RulePool) (vr : VerifiedRule) :
    ∀ vr' ∈ (pool.addRule vr).rules, ∀ env : Nat → Nat,
      vr'.candidate.lhsTemplate.eval env = vr'.candidate.rhsTemplate.eval env := by
  intro vr' hvr' env
  simp [RulePool.addRule] at hvr'
  rcases hvr' with rfl | hmem
  · exact vr'.sound env
  · exact (rulePool_all_equivalent pool vr' hmem env)

/-- Pool size increases by 1 when adding a rule. -/
theorem addRule_size (pool : RulePool) (vr : VerifiedRule) :
    (pool.addRule vr).size = pool.size + 1 := by
  simp [RulePool.addRule, RulePool.size, List.length_cons]

/-- Empty pool has size 0. -/
theorem empty_size : RulePool.empty.size = 0 := rfl

-- ============================================================
-- Convert pool to pipeline-compatible format
-- ============================================================

/-- Convert a VerifiedRule to a SoundRewriteRule for the pipeline.
    Uses the candidate's templates as LHS/RHS expressions. -/
def VerifiedRule.toSoundRewriteRule (vr : VerifiedRule) : SoundRewriteRule CryptoOp CryptoExpr Nat where
  name := vr.candidate.name
  rule := {  -- Dummy rule pattern (actual e-matching handled separately)
    name := vr.candidate.name
    lhs := .patVar 0
    rhs := .patVar 0
  }
  lhsExpr := fun _ => vr.candidate.lhsTemplate
  rhsExpr := fun _ => vr.candidate.rhsTemplate
  eval := cryptoEval
  soundness := by
    intro env _
    exact vr.sound env

/-- Get all rules from the pool as SoundRewriteRules. -/
def RulePool.toSoundRules (pool : RulePool) : List (SoundRewriteRule CryptoOp CryptoExpr Nat) :=
  pool.rules.map VerifiedRule.toSoundRewriteRule

-- ============================================================
-- Performance budget enforcement (D13)
-- ============================================================

/-- Add a rule only if it passes the performance budget. -/
def RulePool.addIfBudget (pool : RulePool) (vr : VerifiedRule)
    (threshold : Nat := 10) : RulePool × Bool :=
  if vr.candidate.passesPerformanceBudget threshold then
    (pool.addRule vr, true)
  else
    (pool, false)

-- ============================================================
-- Concrete examples
-- ============================================================

/-- Example pool with the two manually verified rules. -/
def examplePool : RulePool :=
  RulePool.empty
    |>.addRule verifiedSpnBridge
    |>.addRule verifiedRoundDecomp

-- Smoke tests
#eval examplePool.size                           -- 2
#eval examplePool.toSoundRules.length            -- 2
#eval (examplePool.removeByName "spnBlockBridge").size  -- 1

/-- Non-vacuity: pool with 2 rules, all sound. -/
example : ∀ vr ∈ examplePool.rules, ∀ env : Nat → Nat,
    vr.candidate.lhsTemplate.eval env = vr.candidate.rhsTemplate.eval env :=
  rulePool_all_equivalent examplePool

end SuperHash
