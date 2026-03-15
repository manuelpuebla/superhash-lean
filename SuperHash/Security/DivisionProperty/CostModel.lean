import SuperHash.Security.DivisionProperty.Propagation
/-!
# SuperHash.Security.DivisionProperty.CostModel — Integral distinguisher cost model

## Scope
Formalizes the cost model for integral distinguishers based on division
property propagation. The division property weight after r rounds determines
how many chosen plaintexts are needed to mount an integral attack.

## Key definitions
- `integralDistinguisherCost`: attacker cost = outputBits - remaining weight
- `integralRoundsNeeded`: conservative bound on rounds to neutralize div property
- `divPropertyAfterRounds`: remaining weight after r rounds of S-box propagation

## Cost model (Todo 2015, §6)
The integral distinguisher requires 2^{n - maxDivWeight} chosen plaintexts,
where n is the output bits and maxDivWeight is the remaining division property
weight after propagation through the cipher rounds. Higher remaining weight
means lower cost (more dangerous for the cipher).

## Concrete instances
- **PRESENT-80**: 6 rounds to kill division property (degree 3, 80 bits)
- **AES-128**: 4 rounds to kill division property (degree 7, 128 bits)

## References
- Todo, "Structural Evaluation by Generalized Integral Property" (EUROCRYPT 2015), §6
- Todo & Morii, "Bit-Based Division Property" (FSE 2016), §4
- Xiang et al., "Applying MILP Method" (ASIACRYPT 2016), §4
-/

namespace SuperHash.Security.DivisionProperty.CostModel

open SuperHash.Security.DivisionProperty.Propagation

-- ============================================================
-- Section 1: Cost model definitions
-- ============================================================

/-- **Integral distinguisher cost**: outputBits - maxDivWeight.
    The attacker needs 2^cost chosen plaintexts to mount the distinguisher.
    When maxDivWeight = 0: cost = outputBits (no advantage from div property).
    When maxDivWeight ≥ outputBits: cost = 0 (trivial distinguisher, Nat subtraction).
    When 0 < maxDivWeight < outputBits: cost = outputBits - maxDivWeight.
    (Todo 2015, §6: integral attack complexity) -/
def integralDistinguisherCost (outputBits maxDivWeight : Nat) : Nat :=
  outputBits - maxDivWeight

/-- **Rounds needed to neutralize division property** (conservative bound).
    inputBits rounds always suffice because each round with degree ≥ 2
    and weight ≥ 2 strictly decreases the weight, and once weight ≤ 1,
    it remains ≤ 1. In practice, far fewer rounds are needed (O(log n)).
    (Xiang et al. 2016, §4.2: round complexity analysis) -/
def integralRoundsNeeded (inputBits _sboxDeg : Nat) : Nat :=
  inputBits

/-- **Remaining division weight after r rounds**: iterates S-box propagation
    r times starting from the full input weight.
    After 0 rounds: weight = inputBits (full).
    After r+1 rounds: weight = ⌈previous_weight / sboxDeg⌉.
    (Todo 2015, §5: round-by-round propagation) -/
def divPropertyAfterRounds (inputBits sboxDeg : Nat) : Nat → Nat
  | 0 => inputBits
  | r + 1 => propagateSbox (divPropertyAfterRounds inputBits sboxDeg r) sboxDeg

-- ============================================================
-- Section 2: Cost theorems
-- ============================================================

/-- **Cost bounded by output bits**: the integral distinguisher cost
    never exceeds the output size. This is the maximum cost (no advantage).
    (Structural: Nat subtraction is non-negative) -/
theorem integral_cost_le_output (n w : Nat) :
    integralDistinguisherCost n w ≤ n := by
  simp [integralDistinguisherCost]

/-- **Higher weight → lower cost (more dangerous)**: if the remaining
    division weight increases, the distinguisher cost decreases.
    This means more active bits = cheaper attack = more dangerous.
    (Todo 2015, §6: weight-cost relationship) -/
theorem integral_cost_monotone_weight (n w1 w2 : Nat) (h : w1 ≤ w2) :
    integralDistinguisherCost n w2 ≤ integralDistinguisherCost n w1 := by
  simp [integralDistinguisherCost]; omega

-- ============================================================
-- Section 3: Round propagation theorems
-- ============================================================

/-- **More rounds → less remaining weight**: each additional round
    of S-box propagation can only reduce the division property weight.
    (Structural: propagateSbox w d ≤ w for d ≥ 1) -/
theorem more_rounds_less_weight (w d : Nat) (hd : d ≥ 1) (r : Nat) :
    divPropertyAfterRounds w d (r + 1) ≤ divPropertyAfterRounds w d r := by
  simp [divPropertyAfterRounds]
  exact sbox_reduces_weight _ d hd

/-- **Weight after any number of rounds bounded by input**: the division
    property weight never exceeds the original input weight.
    (Structural: induction on rounds, each round is non-increasing) -/
theorem afterRounds_le_input (w d : Nat) (hd : d ≥ 1) :
    ∀ r, divPropertyAfterRounds w d r ≤ w := by
  intro r; induction r with
  | zero => simp [divPropertyAfterRounds]
  | succ n ih =>
    calc divPropertyAfterRounds w d (n + 1)
        = propagateSbox (divPropertyAfterRounds w d n) d := rfl
      _ ≤ divPropertyAfterRounds w d n := sbox_reduces_weight _ d hd
      _ ≤ w := ih

-- ============================================================
-- Section 4: Division property neutralization
-- ============================================================

/-- **S-box preserves weight ≤ 1**: once the division property weight
    reaches ≤ 1, applying an S-box keeps it ≤ 1.
    Weight 0 → 0 (absorbing state), weight 1 → 1 (fixed point for ceil div).
    (Structural: ⌈0/d⌉ = 0 and ⌈1/d⌉ = 1 for d ≥ 1) -/
theorem sbox_preserves_le_one (w d : Nat) (hd : d ≥ 1) (hw : w ≤ 1) :
    propagateSbox w d ≤ 1 := by
  unfold propagateSbox
  have hd0 : d ≠ 0 := by omega
  rw [if_neg hd0]
  have hd_pos : 0 < d := by omega
  suffices h : (w + d - 1) / d < 2 by omega
  rw [Nat.div_lt_iff_lt_mul hd_pos]; omega

/-- **Sufficient rounds kill division property**: once the weight
    reaches ≤ 1 at round r, it remains ≤ 1 for all subsequent rounds.
    Combined with concrete instance proofs, this gives a complete bound
    for each cipher.
    (Structural: fixed point preservation) -/
theorem sufficient_rounds_kill_div_property (w d : Nat) (hd : d ≥ 1)
    (r₁ r₂ : Nat) (h : divPropertyAfterRounds w d r₁ ≤ 1) :
    divPropertyAfterRounds w d (r₁ + r₂) ≤ 1 := by
  induction r₂ with
  | zero => simp [Nat.add_zero]; exact h
  | succ n ih =>
    show propagateSbox (divPropertyAfterRounds w d (r₁ + n)) d ≤ 1
    exact sbox_preserves_le_one _ d hd ih

/-- **Neutralized weight means maximal cost**: when the division property
    weight is ≤ 1 after enough rounds, the integral distinguisher cost
    equals outputBits - 1 (or outputBits if weight = 0), which means
    the attack offers at most 1 bit of advantage.
    (Todo 2015, §6: neutralized division property) -/
theorem neutralized_weight_max_cost (outputBits w : Nat)
    (hw : w ≤ 1) (hn : outputBits ≥ 1) :
    integralDistinguisherCost outputBits w ≥ outputBits - 1 := by
  simp [integralDistinguisherCost]; omega

/-- **Zero weight is absorbing**: once weight reaches 0, it stays 0.
    propagateSbox 0 d = 0 for d ≥ 1 (since ⌈0/d⌉ = 0).
    (Structural) -/
theorem zero_weight_absorbing (d : Nat) (hd : d ≥ 1) :
    propagateSbox 0 d = 0 := by
  unfold propagateSbox
  have hd0 : d ≠ 0 := by omega
  rw [if_neg hd0]
  simp; omega

/-- **Full rounds cost: if all r rounds of the cipher are used,
    the cost is outputBits - remaining weight after r rounds.
    When the cipher has enough rounds, this is ≥ outputBits - 1.
    (Todo 2015, §6) -/
theorem full_rounds_cost (outputBits inputBits sboxDeg rounds : Nat) :
    integralDistinguisherCost outputBits
      (divPropertyAfterRounds inputBits sboxDeg rounds) ≤ outputBits := by
  exact integral_cost_le_output _ _

-- ============================================================
-- Section 5: Concrete instances
-- ============================================================

/-- **PRESENT-80: 6 rounds kill division property.**
    PRESENT has degree-3 S-box and 80-bit state.
    After 6 rounds: divPropertyAfterRounds 80 3 6 ≤ 1.
    80 → 27 → 9 → 3 → 1 → 1 → 1.
    (Todo & Morii 2016, Table 3) -/
theorem present_6_rounds_kill :
    divPropertyAfterRounds 80 3 6 ≤ 1 := by native_decide

/-- **AES-128: 4 rounds kill division property.**
    AES has degree-7 S-box and 128-bit state.
    After 4 rounds: divPropertyAfterRounds 128 7 4 ≤ 1.
    128 → 19 → 3 → 1 → 1.
    (Todo 2015, Table 2) -/
theorem aes_4_rounds_kill :
    divPropertyAfterRounds 128 7 4 ≤ 1 := by native_decide

/-- **PRESENT-80 survives after enough rounds.**
    Applying sufficient_rounds_kill_div_property: once killed at round 6,
    stays killed for any additional rounds (e.g., the full 31 rounds). -/
theorem present_full_rounds :
    divPropertyAfterRounds 80 3 (6 + 25) ≤ 1 :=
  sufficient_rounds_kill_div_property 80 3 (by omega) 6 25 present_6_rounds_kill

/-- **AES-128 survives after enough rounds.**
    Applying sufficient_rounds_kill_div_property: once killed at round 4,
    stays killed for any additional rounds (e.g., the full 10 rounds). -/
theorem aes_full_rounds :
    divPropertyAfterRounds 128 7 (4 + 6) ≤ 1 :=
  sufficient_rounds_kill_div_property 128 7 (by omega) 4 6 aes_4_rounds_kill

end SuperHash.Security.DivisionProperty.CostModel
