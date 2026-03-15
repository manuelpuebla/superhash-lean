import SuperHash.Security.DivisionProperty.Spec
/-!
# SuperHash.Security.DivisionProperty.Propagation — Division property propagation rules

## Scope
Formalizes the three fundamental propagation rules for division property
through basic operations (COPY, AND, XOR) and composite operations
(S-box, linear layer, full round). These rules determine how the division
property weight evolves through each cipher component.

## Propagation rules (Todo 2015, §4)
- **COPY**: input weight k → outputs (k, 0), weight conserved
- **AND**: min(k₁, k₂) — AND gate reduces weight
- **XOR**: max(k₁, k₂) — XOR gate preserves maximum
- **S-box**: ⌈inputWeight / degree⌉ — algebraic degree limits propagation
- **Linear layer**: weight preserved (invertible linear maps)
- **Round**: composition of S-box layer + linear layer

## References
- Todo, "Structural Evaluation by Generalized Integral Property" (EUROCRYPT 2015), §4
- Todo & Morii, "Bit-Based Division Property" (FSE 2016), §3
- Xiang et al., "Applying MILP Method" (ASIACRYPT 2016), §3
-/

namespace SuperHash.Security.DivisionProperty.Propagation

-- ============================================================
-- Section 1: Basic gate propagation rules
-- ============================================================

/-- **COPY propagation**: input weight k splits into (k, 0).
    In the worst case for the attacker, all weight goes to one branch.
    Weight is conserved: k₁ + k₂ = k with k₁ = k, k₂ = 0.
    (Todo 2015, Proposition 4, COPY rule) -/
def propagateCopy (k : Nat) : Nat × Nat := (k, 0)

/-- **AND propagation**: AND gate outputs min(k₁, k₂).
    The AND operation can only reduce the division property weight,
    since it requires both inputs to contribute.
    (Todo 2015, Proposition 4, AND rule) -/
def propagateAnd (k₁ k₂ : Nat) : Nat := min k₁ k₂

/-- **XOR propagation**: XOR gate outputs max(k₁, k₂).
    XOR preserves the maximum weight from either input, since
    XOR is linear and either input can carry the division property.
    (Todo 2015, Proposition 4, XOR rule) -/
def propagateXor (k₁ k₂ : Nat) : Nat := max k₁ k₂

-- ============================================================
-- Section 2: Composite operation propagation
-- ============================================================

/-- **S-box propagation**: weight after S-box = ⌈inputWeight / degree⌉.
    An S-box of algebraic degree d maps division property weight w
    to ⌈w/d⌉. Higher degree S-boxes reduce weight faster.
    Uses (w + d - 1) / d for ceiling division.
    (Todo 2015, Theorem 2; Boura & Canteaut 2016) -/
def propagateSbox (inputWeight degree : Nat) : Nat :=
  if degree = 0 then inputWeight
  else (inputWeight + degree - 1) / degree

/-- **Linear layer propagation**: weight preserved.
    Invertible linear maps (MDS matrices, permutations) preserve
    the division property weight exactly.
    (Todo 2015, Proposition 5) -/
def propagateLinear (inputWeight : Nat) : Nat := inputWeight

/-- **Round propagation**: S-box layer followed by linear layer.
    In a substitution-permutation network, one round applies
    numSboxes parallel S-boxes (each of degree sboxDeg) then a
    linear layer. Weight after round = ⌈inputWeight / sboxDeg⌉
    (linear layer preserves the post-S-box weight).
    (Todo 2015, §5, SPN round propagation) -/
def propagateRound (inputWeight sboxDeg numSboxes : Nat) : Nat :=
  if numSboxes = 0 then inputWeight
  else propagateLinear (propagateSbox inputWeight sboxDeg)

-- ============================================================
-- Section 3: Basic gate theorems
-- ============================================================

/-- **COPY weight conservation**: the two outputs of COPY sum to the input.
    k₁ + k₂ = k where (k₁, k₂) = propagateCopy k.
    (Structural: weight is neither created nor destroyed by COPY) -/
theorem copy_weight_conserved (k : Nat) :
    (propagateCopy k).1 + (propagateCopy k).2 = k := by
  simp [propagateCopy]

/-- **AND monotonicity**: AND output ≤ both inputs.
    min(k₁, k₂) ≤ k₁ and min(k₁, k₂) ≤ k₂.
    (Structural: AND can only reduce weight) -/
theorem and_monotone (a b : Nat) :
    propagateAnd a b ≤ a ∧ propagateAnd a b ≤ b := by
  simp [propagateAnd]
  exact ⟨Nat.min_le_left a b, Nat.min_le_right a b⟩

/-- **XOR monotonicity**: XOR output ≥ both inputs.
    max(k₁, k₂) ≥ k₁ and max(k₁, k₂) ≥ k₂.
    (Structural: XOR preserves the maximum) -/
theorem xor_monotone (a b : Nat) :
    a ≤ propagateXor a b ∧ b ≤ propagateXor a b := by
  simp [propagateXor]
  exact ⟨Nat.le_max_left a b, Nat.le_max_right a b⟩

-- ============================================================
-- Section 4: Composite operation theorems
-- ============================================================

/-- **S-box reduces weight**: ⌈w/d⌉ ≤ w when d ≥ 1.
    An S-box of positive degree can only reduce or preserve weight.
    (Todo 2015, Theorem 2: algebraic degree bounds propagation) -/
theorem sbox_reduces_weight (w d : Nat) (hd : d ≥ 1) :
    propagateSbox w d ≤ w := by
  simp [propagateSbox]
  have hd0 : d ≠ 0 := by omega
  simp [hd0]
  -- Need: (w + d - 1) / d ≤ w
  have hd_pos : 0 < d := by omega
  suffices h : (w + d - 1) / d < w + 1 by omega
  rw [Nat.div_lt_iff_lt_mul hd_pos]
  rw [Nat.add_mul]; simp [Nat.one_mul]
  have hwd : w ≤ w * d := Nat.le_mul_of_pos_right w hd_pos
  omega

/-- **Linear layer preserves weight**: output weight = input weight.
    Invertible linear maps are weight-neutral for division property.
    (Todo 2015, Proposition 5) -/
theorem linear_preserves_weight (w : Nat) :
    propagateLinear w = w := rfl

/-- **Round monotonicity with S-boxes**: for any positive number of S-boxes,
    the round output ≤ input weight.
    (Structural: S-box layer followed by linear layer) -/
theorem round_monotone (w d ns : Nat) (hd : d ≥ 1) (hns : ns ≥ 1) :
    propagateRound w d ns ≤ w := by
  simp [propagateRound]
  have hns0 : ns ≠ 0 := by omega
  simp [hns0, propagateLinear]
  exact sbox_reduces_weight w d hd

-- ============================================================
-- Section 5: Multi-round propagation
-- ============================================================

/-- **Multi-round propagation**: iteratively apply round propagation.
    After r rounds, the division property weight is reduced by repeated
    application of ⌈·/d⌉.
    (Todo 2015, §5: round iteration) -/
def multiRoundPropagation (inputWeight sboxDeg : Nat) : Nat → Nat
  | 0 => inputWeight
  | r + 1 => propagateSbox (multiRoundPropagation inputWeight sboxDeg r) sboxDeg

/-- **Multi-round propagation is monotone in rounds**: more rounds →
    less (or equal) remaining weight, when degree ≥ 1.
    (Structural: each round can only reduce weight) -/
theorem multi_round_monotone (w d : Nat) (hd : d ≥ 1) (r : Nat) :
    multiRoundPropagation w d (r + 1) ≤ multiRoundPropagation w d r := by
  simp [multiRoundPropagation]
  exact sbox_reduces_weight _ d hd

/-- **Multi-round propagation bounded by input**: after any number of
    rounds, weight never exceeds the original input weight.
    (Structural: induction on rounds) -/
theorem multi_round_le_input (w d : Nat) (hd : d ≥ 1) :
    ∀ r, multiRoundPropagation w d r ≤ w := by
  intro r
  induction r with
  | zero => simp [multiRoundPropagation]
  | succ n ih =>
    calc multiRoundPropagation w d (n + 1)
        = propagateSbox (multiRoundPropagation w d n) d := rfl
      _ ≤ multiRoundPropagation w d n := sbox_reduces_weight _ d hd
      _ ≤ w := ih

end SuperHash.Security.DivisionProperty.Propagation
