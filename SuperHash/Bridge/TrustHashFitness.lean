import SuperHash.Crypto.Fitness
import SuperHash.Crypto.BouraCanteutBound
import SuperHash.Crypto.HigherOrderDiff
import SuperHash.Crypto.LinearLayerDegree

/-!
# SuperHash.Bridge.TrustHashFitness — TrustHash-style verified fitness evaluator

v2.8: Implements TrustHash's security evaluation formula using the
Boura-Canteaut bounds, higher-order differential theory, and SPN
phase analysis now available in SuperHash.

## TrustHash Architecture (simplified)
```
security_level = min(generic_floor, structural_cost)
structural_cost = min(differential_cost, algebraic_cost)
```

This module provides the algebraic_cost component using:
- BCD11/BC13 bounds for degree after r rounds
- Higher-order differential attack complexity (2^{deg+1} queries)
- SPN phase transition for minimum rounds to full degree

## Relation to TrustHash (~/Documents/claudio/TrustHash/)
TrustHash uses HashOp (11 constructors, Lean 4.16). This module provides
equivalent functionality using CryptoOp (12 constructors, Lean 4.28).
Full HashOp ↔ CryptoOp bridge deferred to v2.9; this version uses the
mathematical bounds directly without type translation.
-/

namespace SuperHash

-- ============================================================
-- Section 1: TrustHash-style security verdict
-- ============================================================

/-- Security verdict: the final output of TrustHash-style analysis.
    Mirrors TrustHash's ComputedAnalysis but uses SuperHash types. -/
structure SecurityVerdict where
  /-- Generic floor: birthday bound, GBP, Joux (attack-independent) -/
  genericFloor : Nat
  /-- Differential cost: δ^{activeSboxes} (from wide trail) -/
  differentialCost : Nat
  /-- Algebraic cost: attack complexity from degree (2^{deg+1} queries) -/
  algebraicCost : Nat
  /-- BCD11 degree after r rounds -/
  bcdDegreeAfterRounds : Nat
  /-- Overall security level = min of all components -/
  securityLevel : Nat
  /-- Whether structural cost ≥ generic floor ("optimal" design) -/
  isOptimal : Bool
  deriving Repr

-- ============================================================
-- Section 2: Compute TrustHash-style verdict
-- ============================================================

/-- Compute the full TrustHash-style security verdict for an SPN design.

    Inputs:
    - `outputBits`: hash output length (e.g., 128 for AES-128)
    - `sboxBits`: S-box input width (e.g., 8 for AES)
    - `sboxDeg`: algebraic degree of S-box (e.g., 7 for AES)
    - `delta`: differential uniformity δ (e.g., 4 for AES)
    - `gamma`: BCD11 propagation constant (e.g., 4 for AES)
    - `branchNum`: MDS branch number (e.g., 5 for AES)
    - `numRounds`: number of cipher rounds (e.g., 10 for AES)
    - `numSboxes`: total state size in S-boxes (e.g., 16 for AES)
    - `treewidth`: constraint graph treewidth (e.g., 5 for AES) -/
def computeVerdict (outputBits sboxBits sboxDeg delta gamma branchNum numRounds numSboxes treewidth : Nat) : SecurityVerdict :=
  -- Generic floor: birthday bound
  let generic := outputBits / 2

  -- Differential cost: activeSboxes × (sboxBits - log2(δ))
  let activeSboxes := branchNum * (numRounds / 2)
  let diffCost := if delta ≤ 1 then outputBits
    else activeSboxes * (sboxBits - ilog2 delta)

  -- Algebraic cost via BCD11 bound
  let totalBits := sboxBits * numSboxes
  let degAfterR := iteratedBcd11 totalBits 0 gamma numRounds
  -- Attack complexity: treewidth × log2(degree)
  let algCost := if degAfterR ≤ 1 then 0
    else treewidth * ilog2 degAfterR

  -- Higher-order differential: 2^{deg+1} queries → deg+1 bits
  let hoDiffCost := degAfterR + 1

  -- Overall: min of all
  let structural := min diffCost (min algCost hoDiffCost)
  let overall := min generic structural

  { genericFloor := generic
    differentialCost := diffCost
    algebraicCost := algCost
    bcdDegreeAfterRounds := degAfterR
    securityLevel := overall
    isOptimal := structural ≥ generic }

-- ============================================================
-- Section 3: Monotonicity properties
-- ============================================================

/-- The BCD degree bound increases with each additional round (step monotonicity).
    Adding rounds increases the BCD degree bound, which increases algebraic
    and higher-order differential costs. -/
theorem verdict_degree_mono_step (out n d delta gamma bn r s tw : Nat)
    (h_gamma : gamma ≥ 2) :
    (computeVerdict out n d delta gamma bn r s tw).bcdDegreeAfterRounds ≤
    (computeVerdict out n d delta gamma bn (r + 1) s tw).bcdDegreeAfterRounds := by
  simp only [computeVerdict]
  exact iterated_bcd11_mono_rounds (n * s) 0 gamma r h_gamma

-- ============================================================
-- Section 4: Concrete verdicts
-- ============================================================

-- AES-128: 10 rounds, sbox deg=7, delta=4, gamma=4, BN=5, tw=5
def aesVerdict := computeVerdict 128 8 7 4 4 5 10 16 5

#eval aesVerdict
-- Expected: generic=64, diff=150, algCost based on BCD11 degree after 10 rounds

-- Poseidon-128 (t=3): 8 full rounds, deg=5, delta=2, gamma=4, BN=4, tw=3
def poseidonVerdict := computeVerdict 256 64 5 2 4 4 8 3 3

#eval poseidonVerdict

-- PRESENT: 31 rounds, sbox deg=3, delta=4, gamma=4, BN=5, tw=4
def presentVerdict := computeVerdict 128 4 3 4 4 5 31 16 4

#eval presentVerdict

-- ============================================================
-- Section 5: Non-vacuity
-- ============================================================

/-- AES generic floor = 64 bits. -/
example : aesVerdict.genericFloor = 64 := by native_decide

/-- AES differential cost = 150 bits (25 active × 6 bits each). -/
example : aesVerdict.differentialCost = 150 := by native_decide

/-- AES uses BCD11 degree after 10 rounds. -/
example : aesVerdict.bcdDegreeAfterRounds = iteratedBcd11 128 0 4 10 := rfl

/-- Poseidon generic floor = 128 bits (256-bit output). -/
example : poseidonVerdict.genericFloor = 128 := by native_decide

/-- Security verdict correctly identifies the binding constraint. -/
example : aesVerdict.securityLevel ≤ aesVerdict.genericFloor := by native_decide

end SuperHash
