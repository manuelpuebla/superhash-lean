import SuperHash.Sbox.AutoSboxPipeline
import SuperHash.Pareto.ExtendedMetrics
import SuperHash.Pareto.ExtendedDominance
import SuperHash.Security.ActiveSboxBounds
import SuperHash.Crypto.SecurityNotions

/-!
# SuperHash.Sbox.SboxParetoBridge — Bridge from S-box analysis to 6D Pareto

Connects the concrete S-box certification pipeline to the 6D Pareto system:
  SboxTable → autoSboxPipeline → SboxAnalysis → ExtendedSecurityMetrics

This bridge:
1. Takes a certified SboxAnalysis (from autoSboxPipeline)
2. Computes security bits using wide-trail bounds and algebraic analysis
3. Packages the result as ExtendedSecurityMetrics for Pareto optimization

Key parameters:
- rounds: total rounds of the cipher (full + partial)
- outputBits: hash output size in bits
- branchNumber: MDS matrix branch number (for active S-box lower bound)

End-to-end example: PRESENT S-box table → certified → extended metrics.
-/

namespace SuperHash.Sbox.SboxParetoBridge

open SuperHash
open SuperHash.Sbox
open SuperHash.Sbox.SboxBridge
open SuperHash.Sbox.AutoSboxPipeline
open SuperHash.Security.ActiveSboxBounds

-- ============================================================
-- Section 1: Core bridge function
-- ============================================================

/-- **Compute per-S-box differential entropy: inputBits - ilog2(delta).**
    Same formula as perSboxEntropy from SourceEntropy.lean, but computed
    directly from SboxAnalysis fields.
    Returns 0 if ilog2(delta) >= inputBits (degenerate case). -/
def sboxDiffEntropy (sa : SboxAnalysis) : Nat :=
  if ilog2 sa.diffUniformity ≥ sa.inputBits then 0
  else sa.inputBits - ilog2 sa.diffUniformity

/-- **Compute algebraic security bits from S-box analysis.**
    algebraicBits = ilog2(algebraicDeg^rounds) = rounds * ilog2(algebraicDeg).
    This uses the fact that for GF(2^n) polynomials, the algebraic degree
    of a composition of r rounds is at most deg^r. -/
def sboxAlgBits (sa : SboxAnalysis) (rounds : Nat) : Nat :=
  rounds * ilog2 sa.algebraicDeg

/-- **Convert SboxAnalysis to ExtendedSecurityMetrics.**
    Combines differential and algebraic bounds with birthday bound.

    Parameters:
    - `sa` : certified SboxAnalysis from autoSboxPipeline
    - `rounds` : total cipher rounds
    - `outputBits` : hash output size in bits
    - `activeSboxes` : lower bound on active S-boxes (from wide-trail analysis)

    Security computation (per Rogaway-Shrimpton bridge):
    - diffBits = activeSboxes * (inputBits - ilog2(delta))
    - algBits = rounds * ilog2(algebraicDeg)
    - collisionBits = min(outputBits/2, diffBits, algBits)
    - preImageBits = outputBits (ideal, no structural weakness)
    - secondPreImageBits = outputBits
    - targetCRBits = collisionBits (Coll -> eSec)

    Efficiency (abstract units):
    - latency = rounds (one round per clock tick)
    - gateCount = rounds * 2^inputBits (rough: each round processes domain) -/
def sboxAnalysisToExtended (sa : SboxAnalysis) (rounds outputBits activeSboxes : Nat) :
    ExtendedSecurityMetrics :=
  let diffBits := activeSboxes * sboxDiffEntropy sa
  let algBits := sboxAlgBits sa rounds
  let collBits := min (outputBits / 2) (min diffBits algBits)
  { collisionBits      := collBits
    preImageBits       := outputBits
    secondPreImageBits := outputBits
    targetCRBits       := collBits
    latency            := rounds
    gateCount          := rounds * (2 ^ sa.inputBits) }

-- ============================================================
-- Section 2: Bridge theorems
-- ============================================================

/-- Collision bits are bounded by birthday bound. -/
theorem sboxAnalysisToExtended_collision_le_birthday
    (sa : SboxAnalysis) (rounds outputBits activeSboxes : Nat) :
    (sboxAnalysisToExtended sa rounds outputBits activeSboxes).collisionBits
    ≤ outputBits / 2 := by
  simp [sboxAnalysisToExtended]
  exact Nat.min_le_left _ _

/-- PreImage bits equal output bits (ideal). -/
theorem sboxAnalysisToExtended_preImage
    (sa : SboxAnalysis) (rounds outputBits activeSboxes : Nat) :
    (sboxAnalysisToExtended sa rounds outputBits activeSboxes).preImageBits
    = outputBits := rfl

/-- TargetCR bits equal collision bits (Coll -> eSec). -/
theorem sboxAnalysisToExtended_targetCR_eq_collision
    (sa : SboxAnalysis) (rounds outputBits activeSboxes : Nat) :
    (sboxAnalysisToExtended sa rounds outputBits activeSboxes).targetCRBits =
    (sboxAnalysisToExtended sa rounds outputBits activeSboxes).collisionBits := rfl

/-- Latency equals rounds. -/
theorem sboxAnalysisToExtended_latency
    (sa : SboxAnalysis) (rounds outputBits activeSboxes : Nat) :
    (sboxAnalysisToExtended sa rounds outputBits activeSboxes).latency
    = rounds := rfl

/-- More active S-boxes → more collision bits (monotonicity in activeSboxes). -/
theorem sboxAnalysisToExtended_mono_active (sa : SboxAnalysis)
    (rounds outputBits a1 a2 : Nat) (h : a1 ≤ a2) :
    (sboxAnalysisToExtended sa rounds outputBits a1).collisionBits ≤
    (sboxAnalysisToExtended sa rounds outputBits a2).collisionBits := by
  simp only [sboxAnalysisToExtended]
  have hmul : a1 * sboxDiffEntropy sa ≤ a2 * sboxDiffEntropy sa :=
    Nat.mul_le_mul_right _ h
  omega

-- ============================================================
-- Section 3: Concrete instances
-- ============================================================

/-- PRESENT S-box analysis via autoSboxPipeline. -/
noncomputable def presentSboxAnalysis : SboxAnalysis := autoSboxPipeline presentSbox

/-- PRESENT-64 extended metrics.
    PRESENT: 4-bit S-box, 31 rounds, 64-bit output, BN=5 → 5*6+1=31 active S-boxes (simplified). -/
def presentExtended : ExtendedSecurityMetrics :=
  sboxAnalysisToExtended (analyzeSbox presentSbox) 31 64 31

/-- PRESENT collision bits. -/
theorem present_extended_collision :
    presentExtended.collisionBits = 31 := by native_decide

/-- PRESENT latency = 31 rounds. -/
theorem present_extended_latency :
    presentExtended.latency = 31 := by native_decide

/-- PRESENT preImage = 64 (ideal). -/
theorem present_extended_preImage :
    presentExtended.preImageBits = 64 := by native_decide

/-- Toy 2-bit S-box extended metrics (minimal example). -/
def toy2Extended : ExtendedSecurityMetrics :=
  sboxAnalysisToExtended (analyzeSbox toy2Sbox) 4 8 4

/-- Toy 2-bit: collision bits. -/
theorem toy2_extended_collision :
    toy2Extended.collisionBits = 0 := by native_decide

/-- Toy 3-bit S-box extended metrics. -/
def toy3Extended : ExtendedSecurityMetrics :=
  sboxAnalysisToExtended (analyzeSbox toy3Sbox) 4 16 4

-- ============================================================
-- Section 4: End-to-end example
-- ============================================================

/-- **End-to-end: PRESENT S-box table → certified analysis → extended metrics.**
    Demonstrates the full pipeline from a raw S-box lookup table through
    certified DDT/LAT/degree computation to 6D Pareto-ready metrics. -/
def presentEndToEnd : ExtendedSecurityMetrics :=
  let sa := analyzeSbox presentSbox  -- SboxTable → SboxAnalysis (certified)
  sboxAnalysisToExtended sa 31 64 31  -- SboxAnalysis → ExtendedSecurityMetrics

/-- End-to-end produces same result as direct construction. -/
theorem presentEndToEnd_eq : presentEndToEnd = presentExtended := rfl

/-- End-to-end: collision bits are bounded by birthday. -/
theorem presentEndToEnd_collision_le :
    presentEndToEnd.collisionBits ≤ 64 / 2 := by native_decide

/-- End-to-end: PRESENT is not dominated by toy2. -/
theorem present_not_dominated_by_toy2 :
    ¬ extDominates toy2Extended presentExtended := by
  native_decide

-- ============================================================
-- Section 5: Non-vacuity examples
-- ============================================================

/-- Non-vacuity 1: sboxAnalysisToExtended is inhabited with PRESENT. -/
example : ExtendedSecurityMetrics :=
  sboxAnalysisToExtended (analyzeSbox presentSbox) 31 64 31

/-- Non-vacuity 2: PRESENT extended metrics have concrete collision bits. -/
example : (sboxAnalysisToExtended (analyzeSbox presentSbox) 31 64 31).collisionBits = 31 := by
  native_decide

/-- Non-vacuity 3: monotonicity is satisfiable with concrete values. -/
example : (sboxAnalysisToExtended (analyzeSbox presentSbox) 31 64 20).collisionBits ≤
          (sboxAnalysisToExtended (analyzeSbox presentSbox) 31 64 31).collisionBits :=
  sboxAnalysisToExtended_mono_active (analyzeSbox presentSbox) 31 64 20 31 (by omega)

-- Smoke tests
#eval presentExtended
#eval toy2Extended
#eval toy3Extended
#eval presentEndToEnd

end SuperHash.Sbox.SboxParetoBridge
