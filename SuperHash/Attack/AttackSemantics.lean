import SuperHash.Attack.AttackOp

/-!
# SuperHash.Attack.AttackSemantics — Attack semantic domain and evaluator

Defines `AttackSemantics`, the Red Team counterpart to `CryptoSemantics`.
Each field captures a measurable property of a cryptanalytic attack.

## AttackSemantics fields
- `timeCost`: log2 of time complexity (lower is better for attacker)
- `memoryCost`: log2 of memory complexity
- `dataCost`: log2 of chosen/known texts needed
- `successProb`: -log2 of success probability (lower = more likely)
- `roundsCovered`: number of cipher rounds the attack covers

## Composition algebra
- `compose` (sequential): time ADDS, memory MAX, data MAX, prob ADDS, rounds ADD
- `parallel` (independent): time MIN, memory MIN, data MIN, prob MIN, rounds MAX
- `iterate(n)`: time n*, memory same, data same, prob n*, rounds n*

## Design
Follows the same pattern as CryptoEval.lean but with attack-specific semantics.
Uses `Inhabited` with default (all zeros), not Option (L-376).
-/

namespace SuperHash

-- ============================================================
-- Section 1: AttackSemantics — THE CORE TYPE
-- ============================================================

/-- The attack semantic domain. Each field captures a measurable
    property of a cryptanalytic attack strategy.

    This is the Red Team counterpart to CryptoSemantics (Blue Team).
    Every attack node in the E-graph evaluates to an AttackSemantics
    value, enabling cost-optimal attack composition. -/
structure AttackSemantics where
  /-- Log2 of time complexity. Lower is better for attacker.
      E.g., timeCost=80 means 2^80 operations. -/
  timeCost : Nat
  /-- Log2 of memory complexity.
      E.g., memoryCost=40 means 2^40 memory units. -/
  memoryCost : Nat
  /-- Log2 of chosen/known texts needed.
      E.g., dataCost=64 means 2^64 texts. -/
  dataCost : Nat
  /-- Negative log2 of success probability. Lower = more likely.
      E.g., successProb=10 means probability 2^{-10}. -/
  successProb : Nat
  /-- Number of cipher rounds the attack covers.
      Higher means more powerful attack. -/
  roundsCovered : Nat
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited

-- ============================================================
-- Section 2: Dominance relation (Pareto over AttackSemantics)
-- ============================================================

/-- Attack dominance: attack A dominates B if A is at least as good
    in ALL dimensions and strictly better in at least one.
    For the attacker: lower cost is better, more rounds covered is better. -/
def attackDominates (a b : AttackSemantics) : Prop :=
  a.timeCost ≤ b.timeCost ∧
  a.memoryCost ≤ b.memoryCost ∧
  a.dataCost ≤ b.dataCost ∧
  a.successProb ≤ b.successProb ∧
  a.roundsCovered ≥ b.roundsCovered ∧
  (a.timeCost < b.timeCost ∨
   a.memoryCost < b.memoryCost ∨
   a.dataCost < b.dataCost ∨
   a.successProb < b.successProb ∨
   a.roundsCovered > b.roundsCovered)

theorem attackDominates_irrefl (a : AttackSemantics) : ¬attackDominates a a := by
  intro ⟨_, _, _, _, _, h⟩
  rcases h with h | h | h | h | h <;> omega

theorem attackDominates_asymm (a b : AttackSemantics) :
    attackDominates a b → ¬attackDominates b a := by
  intro ⟨h1, h2, h3, h4, h5, h6⟩ ⟨g1, g2, g3, g4, g5, _g6⟩
  rcases h6 with h | h | h | h | h <;> omega

-- ============================================================
-- Section 3: evalAttackSem — Attack evaluator
-- ============================================================

/-- Evaluate an AttackOp node with AttackSemantics domain.

    Each operation computes REAL cryptanalytic metrics:
    - Differential family: probability-based costs
    - Linear family: bias-based costs
    - Algebraic family: degree-based costs
    - Structural family: round-splitting costs
    - Composition: attack-specific algebra (see module doc) -/
def evalAttackSem : AttackOp → List AttackSemantics → AttackSemantics
  -- Differential characteristic: time = 2*prob, memory = prob, data = prob
  -- One round of differential propagation
  | .diffChar p _, [child] =>
    { timeCost := child.timeCost + 2 * p
      memoryCost := child.memoryCost + p
      dataCost := child.dataCost + p
      successProb := child.successProb + p
      roundsCovered := child.roundsCovered + 1 }

  -- Truncated differential: fewer active bytes reduces cost
  | .truncatedDiff ab _, [child] =>
    { timeCost := child.timeCost + ab
      memoryCost := child.memoryCost + ab
      dataCost := child.dataCost + ab
      successProb := child.successProb + ab / 2  -- truncation improves probability
      roundsCovered := child.roundsCovered + 1 }

  -- Boomerang: combines two differentials (top + bottom)
  -- time = child1.time + child2.time + 1, prob = sum, rounds = sum
  | .boomerang _ _, [child1, child2] =>
    { timeCost := child1.timeCost + child2.timeCost + 1
      memoryCost := max child1.memoryCost child2.memoryCost
      dataCost := max child1.dataCost child2.dataCost + 1
      successProb := child1.successProb + child2.successProb
      roundsCovered := child1.roundsCovered + child2.roundsCovered }

  -- Impossible differential: rounds are "free" (contradiction-based)
  | .impossible r _, [child] =>
    { timeCost := child.timeCost + r
      memoryCost := child.memoryCost + r
      dataCost := child.dataCost
      successProb := child.successProb  -- deterministic (contradiction)
      roundsCovered := child.roundsCovered + r }

  -- Linear trail: bias determines complexity
  | .linearTrail b _, [child] =>
    { timeCost := child.timeCost + 2 * b
      memoryCost := child.memoryCost
      dataCost := child.dataCost + 2 * b  -- Matsui's algorithm needs 2^{2b} texts
      successProb := child.successProb + b
      roundsCovered := child.roundsCovered + 1 }

  -- Linear hull: aggregation of multiple trails improves bias
  | .linearHull nt _, [child] =>
    { timeCost := child.timeCost + nt  -- cost of aggregation
      memoryCost := child.memoryCost + nt
      dataCost := child.dataCost + nt
      successProb := if child.successProb > nt / 2
                     then child.successProb - nt / 2  -- hull improves prob
                     else 0
      roundsCovered := child.roundsCovered + 1 }

  -- Algebraic relation: degree determines system complexity
  | .algebraicRelation d _, [child] =>
    { timeCost := child.timeCost + d * d  -- quadratic in degree
      memoryCost := child.memoryCost + d
      dataCost := child.dataCost
      successProb := child.successProb
      roundsCovered := child.roundsCovered + 1 }

  -- Grobner basis step: expensive but deterministic
  | .grobnerStep _, [child] =>
    { timeCost := child.timeCost + 3  -- omega(d^w) but simplified
      memoryCost := child.memoryCost + 3
      dataCost := child.dataCost
      successProb := child.successProb  -- deterministic
      roundsCovered := child.roundsCovered }

  -- Meet-in-the-middle: split cipher at splitRound
  | .meetInMiddle sr _ _, [child1, child2] =>
    { timeCost := max child1.timeCost child2.timeCost + sr
      memoryCost := child1.memoryCost + child2.memoryCost  -- both halves in memory
      dataCost := max child1.dataCost child2.dataCost
      successProb := child1.successProb + child2.successProb
      roundsCovered := child1.roundsCovered + child2.roundsCovered }

  -- Rebound: inbound phase (free) + outbound phase (costly)
  | .rebound ir or_ _, [child] =>
    { timeCost := child.timeCost + or_
      memoryCost := child.memoryCost + ir
      dataCost := child.dataCost + or_
      successProb := child.successProb + or_
      roundsCovered := child.roundsCovered + ir + or_ }

  -- Sequential composition: time ADDS, memory MAX, data MAX, prob ADDS
  | .compose _ _, [first, second] =>
    { timeCost := first.timeCost + second.timeCost
      memoryCost := max first.memoryCost second.memoryCost
      dataCost := max first.dataCost second.dataCost
      successProb := first.successProb + second.successProb
      roundsCovered := first.roundsCovered + second.roundsCovered }

  -- Parallel (independent attacks): take the BEST (MIN) in each dimension
  | .parallel _ _, [left, right] =>
    { timeCost := min left.timeCost right.timeCost
      memoryCost := min left.memoryCost right.memoryCost
      dataCost := min left.dataCost right.dataCost
      successProb := min left.successProb right.successProb
      roundsCovered := max left.roundsCovered right.roundsCovered }

  -- Iterate: repeat attack n times
  | .iterate n _, [body] =>
    { timeCost := n * body.timeCost
      memoryCost := body.memoryCost  -- memory reused
      dataCost := body.dataCost      -- data reused
      successProb := n * body.successProb
      roundsCovered := n * body.roundsCovered }

  -- Constant: base attack with fixed cost
  | .const cost, [] =>
    { timeCost := cost
      memoryCost := 0
      dataCost := 0
      successProb := 0
      roundsCovered := 0 }

  -- FALLBACK: malformed node (wrong child count).
  | _, _ => default

-- ============================================================
-- Section 4: Concrete attack instances
-- ============================================================

/-- A basic differential characteristic against 1 round with prob 2^{-6}. -/
def basicDiffAttack : AttackSemantics where
  timeCost := 12    -- 2 * 6
  memoryCost := 6
  dataCost := 6
  successProb := 6
  roundsCovered := 1

/-- Matsui's linear attack against 1 round with bias 2^{-14}. -/
def basicLinearAttack : AttackSemantics where
  timeCost := 28    -- 2 * 14
  memoryCost := 0
  dataCost := 28    -- 2^{2*14} texts
  successProb := 14
  roundsCovered := 1

/-- Boomerang attack combining two 3-round differentials. -/
def boomerangExample : AttackSemantics where
  timeCost := 25    -- combined top + bottom + 1
  memoryCost := 10  -- max of both halves
  dataCost := 11    -- max + 1
  successProb := 16 -- sum of both probs
  roundsCovered := 6

-- ============================================================
-- Section 5: Smoke tests
-- ============================================================

-- diffChar: prob=6, child has zero cost → time=12, mem=6, data=6, prob=6, rounds=1
#eval evalAttackSem (.diffChar 6 0) [⟨0, 0, 0, 0, 0⟩]
-- Expected: {time=12, mem=6, data=6, prob=6, rounds=1}

-- boomerang: two children → combined
#eval evalAttackSem (.boomerang 0 1)
  [⟨10, 5, 5, 8, 3⟩,   -- top differential
   ⟨14, 8, 6, 8, 3⟩]   -- bottom differential
-- Expected: {time=25, mem=8, data=7, prob=16, rounds=6}

-- compose: sequential
#eval evalAttackSem (.compose 0 1)
  [⟨12, 6, 6, 6, 1⟩,
   ⟨28, 0, 28, 14, 1⟩]
-- Expected: {time=40, mem=6, data=28, prob=20, rounds=2}

-- parallel: take best
#eval evalAttackSem (.parallel 0 1)
  [⟨12, 6, 6, 6, 1⟩,
   ⟨28, 0, 28, 14, 1⟩]
-- Expected: {time=12, mem=0, data=6, prob=6, rounds=1}

-- iterate 10: time*10, prob*10, rounds*10
#eval evalAttackSem (.iterate 10 0) [⟨12, 6, 6, 6, 1⟩]
-- Expected: {time=120, mem=6, data=6, prob=60, rounds=10}

-- const: base cost
#eval evalAttackSem (.const 128) []
-- Expected: {time=128, mem=0, data=0, prob=0, rounds=0}

-- meetInMiddle: split at round 4
#eval evalAttackSem (.meetInMiddle 4 0 1)
  [⟨20, 10, 8, 5, 4⟩,
   ⟨18, 12, 6, 3, 4⟩]
-- Expected: {time=24, mem=22, data=8, prob=8, rounds=8}

-- FALLBACK DETECTION: malformed nodes produce zero-cost (default)
#eval (evalAttackSem (.compose 0 0) [⟨5, 5, 5, 5, 1⟩]).timeCost  -- 0 (needs 2 children)
#eval (evalAttackSem (.diffChar 6 0) []).timeCost                   -- 0 (needs 1 child)

end SuperHash
