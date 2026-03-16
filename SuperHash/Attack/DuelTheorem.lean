import SuperHash.Attack.HashSpecBridge
import SuperHash.DesignParams
import SuperHash.Rules.CryptoRules
import SuperHash.Crypto.Fitness
import SuperHash.Pipeline.Instances

/-!
# SuperHash.Attack.DuelTheorem — THE Crown Jewel (v4.5.2)

The duel theorem captures the fundamental guarantee of the SuperHash framework:
**every Blue Team design is at least as secure as every Red Team attack is costly.**

## v4.5.2 — Block B
- `h_blue` relaxed from `=` to `≤` (design security ≤ defense level)
- `pipeline_duel` conclusion strengthened: now returns both security bound AND
  coverage guarantee (`a.2.roundsCovered ≥ spec.numRounds`)
- `duel_security_nondecreasing` replaced: uses `verdict_security_mono_rounds`
  instead of tautological `h_generic_binding` hypotheses

## v4.5.1 — Correccion 1
- `designSecurityLevel` now GENUINELY depends on the design via `evaluateDesign`
  (was phantom parameter before — always returned `defenseSecurityLevel spec`)
- `pipeline_duel` takes `env : Nat → CryptoSemantics` and uses real evaluation
- `h_blue` requires proving that the design evaluation is bounded by defense level
- `h_coverage` is used in the conclusion (coverage guarantee)

## Proof
Via calc chain: h_blue → defense_eq_attack_bound → h_red.
The bridge theorem is now proven by structural unfolding, not `rfl`.

## Co-evolution
`duel_security_nondecreasing`: when more rounds increase defense level,
the Blue Team's security doesn't decrease across co-evolution rounds.
Uses `verdict_security_mono_rounds` for the complete proof.
-/

namespace SuperHash

open TrustHash

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Design security level
-- ══════════════════════════════════════════════════════════════════

/-- Extract a `DesignConfig` from a `HashSpec` for fitness evaluation.
    Bridges the TrustHash specification world to the Fitness evaluation world. -/
def specToConfig (spec : HashSpec) : DesignConfig :=
  { outputBits := spec.outputBits, sboxBits := spec.sboxBits, treewidth := spec.tree.treewidth }

/-- Design security level: evaluates the CryptoExpr design to CryptoSemantics
    via `evalCS`, then computes fitness via `evaluateDesign`.
    v4.5.1: genuinely depends on the design (was phantom before). -/
def designSecurityLevel (design : CryptoExpr) (spec : HashSpec)
    (env : Nat → CryptoSemantics) : Nat :=
  evaluateDesign (specToConfig spec) (CryptoExpr.evalCS design env)

-- ══════════════════════════════════════════════════════════════════
-- Section 2: THE DUEL THEOREM
-- ══════════════════════════════════════════════════════════════════

/-- **Pipeline Duel Theorem (v4.5.2).**

    The crown jewel of the SuperHash framework. States that if:
    - Blue Team designs are bounded by the defense security level (genuinely evaluated)
    - Red Team attacks cost at least the attack cost lower bound
    - Red Team attacks cover all rounds of the cipher

    Then every Blue design's security ≤ every Red attack's cost, AND
    every Red attack covers all cipher rounds.

    v4.5.2: `h_blue` relaxed from `=` to `≤` (more natural: design security is
    bounded by the defense level, not necessarily equal). Conclusion strengthened
    with coverage guarantee from `h_coverage`.
    v4.5.1: `designSecurityLevel` depends on the actual design via `evaluateDesign`. -/
theorem pipeline_duel
    (spec : HashSpec)
    (blue_output : List (CryptoExpr × SecurityMetrics))
    (red_output : List (AttackExpr × AttackMetrics))
    (env : Nat → CryptoSemantics)
    (h_blue : ∀ p ∈ blue_output, designSecurityLevel p.1 spec env ≤ defenseSecurityLevel spec)
    (h_red : ∀ p ∈ red_output, p.2.timeCost ≥ attackCostLowerBound spec)
    (h_coverage : ∀ p ∈ red_output, p.2.roundsCovered ≥ spec.numRounds) :
    ∀ d ∈ blue_output, ∀ a ∈ red_output,
      designSecurityLevel d.1 spec env ≤ a.2.timeCost ∧
      a.2.roundsCovered ≥ spec.numRounds := by
  intro d hd a ha
  constructor
  · calc designSecurityLevel d.1 spec env
        ≤ defenseSecurityLevel spec := h_blue d hd
      _ = attackCostLowerBound spec := defense_eq_attack_bound spec
      _ ≤ a.2.timeCost := h_red a ha
  · exact h_coverage a ha

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Co-evolution monotonicity
-- ══════════════════════════════════════════════════════════════════

/-- **Blue security doesn't decrease across co-evolution rounds.**
    If spec2 has at least as many rounds as spec1, and the same
    crypto parameters (output bits, branch number, S-box bits, delta,
    numSboxes, gamma, tree, sboxDeg), then the defense level doesn't decrease.

    This holds because `defenseSecurityLevel = (computeFullVerdict spec).security`
    and `verdict_security_mono_rounds` proves that the verdict security is
    monotone in rounds when all other parameters are equal. The proof composes:
    - Generic floor: depends only on outputBits (invariant)
    - Differential cost: monotone in rounds (wide trail)
    - Algebraic cost: monotone in rounds (BCD11 iterated degree)
    - DP cost: depends only on tree + delta + sboxDeg (invariant)
    - Higher-order cost: monotone in rounds (iterated degree) -/
theorem duel_security_nondecreasing
    (spec1 spec2 : HashSpec)
    (h_output : spec1.outputBits = spec2.outputBits)
    (h_params : spec1.branchNumber = spec2.branchNumber ∧
                spec1.sboxBits = spec2.sboxBits ∧
                spec1.delta = spec2.delta ∧
                spec1.numSboxes = spec2.numSboxes ∧
                spec1.gamma = spec2.gamma ∧
                spec1.tree = spec2.tree ∧
                spec1.sboxDeg = spec2.sboxDeg)
    (h_gamma : spec1.gamma ≥ 2)
    (h_more_rounds : spec1.numRounds ≤ spec2.numRounds) :
    defenseSecurityLevel spec1 ≤ defenseSecurityLevel spec2 := by
  simp only [defenseSecurityLevel]
  exact verdict_security_mono_rounds spec1 spec2 h_output h_params h_gamma h_more_rounds

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Non-vacuity examples
-- ══════════════════════════════════════════════════════════════════

/-- Concrete HashSpec for non-vacuity testing. -/
private def testSpec : HashSpec := aesSpec

/-- Concrete semantics calibrated so that
    `evaluateDesign (specToConfig aesSpec) matchingSemantics = defenseSecurityLevel aesSpec`.
    deg=128 → ilog2=7, treewidth=7 → alg=49 = defenseSecurityLevel aesSpec.
    δ=1 → diff=128 (ideal). birthday=64. min(64,128,49) = 49. -/
private def matchingSemantics : CryptoSemantics where
  algebraicDegree := 128
  differentialUniformity := 1
  linearBias := 0
  branchNumber := 5
  activeMinSboxes := 25
  latency := 10
  gateCount := 50

/-- Concrete env mapping vars to calibrated semantics. -/
private def testEnv : Nat → CryptoSemantics := fun _ => matchingSemantics

/-- Concrete blue output (design via var that evaluates to matching semantics). -/
private def testBlue : List (CryptoExpr × SecurityMetrics) :=
  [(.var 0, ⟨49, 10, 100⟩)]

/-- Concrete red output (attack costing at least AES lower bound). -/
private def testRed : List (AttackExpr × AttackMetrics) :=
  [(.const 128, ⟨128, 64, 64, 10⟩)]

-- Smoke tests: verify designSecurityLevel depends on actual design
#eval designSecurityLevel (.var 0) aesSpec testEnv  -- should be 49
#eval defenseSecurityLevel aesSpec                  -- should be 49
-- Different design → different security level (not phantom!)
#eval designSecurityLevel (.const 1) aesSpec testEnv  -- should differ

/-- Non-vacuity: pipeline_duel hypotheses are jointly satisfiable.
    v4.5.2: h_blue uses ≤ (easier to satisfy than =).
    Conclusion now includes coverage guarantee. -/
example : ∀ d ∈ testBlue, ∀ a ∈ testRed,
    designSecurityLevel d.1 testSpec testEnv ≤ a.2.timeCost ∧
    a.2.roundsCovered ≥ testSpec.numRounds := by
  apply pipeline_duel testSpec testBlue testRed testEnv
  · intro p hp
    simp [testBlue] at hp; subst hp
    native_decide
  · intro p hp
    simp [testRed] at hp; subst hp
    native_decide
  · intro p hp
    simp [testRed] at hp; subst hp
    simp [testSpec, aesSpec]

/-- AES spec with 12 rounds (for monotonicity non-vacuity). -/
private def aesSpec12 : HashSpec where
  name := "AES-128-12R"
  outputBits := 128
  sboxBits := 8
  numSboxes := 16
  sboxDeg := 7
  delta := 4
  gamma := 4
  branchNumber := 5
  numRounds := 12
  tree := aesSpec.tree

/-- Non-vacuity: duel_security_nondecreasing is satisfiable.
    v4.5.2: uses verdict_security_mono_rounds — requires all 7 param equalities
    + gamma ≥ 2. Concrete: aesSpec (10 rounds) ≤ aesSpec12 (12 rounds). -/
example : defenseSecurityLevel aesSpec ≤ defenseSecurityLevel aesSpec12 := by
  apply duel_security_nondecreasing aesSpec aesSpec12
  · -- h_output
    native_decide
  · -- h_params: 7-tuple equality (tree uses rfl since aesSpec12.tree := aesSpec.tree)
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · -- h_gamma
    native_decide
  · -- h_more_rounds
    native_decide

-- Smoke tests
#check @pipeline_duel
#check @duel_security_nondecreasing
#check @defense_eq_attack_bound

end SuperHash
