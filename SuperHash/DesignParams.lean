import SuperHash.CryptoOp

/-!
# SuperHash.DesignParams — Design parameters and security metrics

Formalizes the structural parameters of a hash function design,
the algebraic security metric computations, and monotonicity
theorems that justify the E-graph rewrite rules.

Adapted from LeanHash.DesignSpace.
-/

namespace SuperHash

/-- Design parameters for a hash function candidate.
    Well-formedness invariants ensure only meaningful designs. -/
structure DesignParams where
  construction : CryptoConstruction
  stateWidth : Nat
  sboxDegree : Nat
  numRounds : Nat
  branchNumber : Nat
  h_width_pos : stateWidth > 0 := by omega
  h_degree_pos : sboxDegree > 0 := by omega
  h_rounds_pos : numRounds > 0 := by omega

/-- Security and efficiency metrics for a hash design.
    Three objectives: securityBits (↑), latency (↓), gateCount (↓). -/
structure SecurityMetrics where
  securityBits : Nat
  latency : Nat
  gateCount : Nat
  deriving Repr, DecidableEq, BEq, Hashable

-- ============================================================
-- Security Metric Computations
-- ============================================================

/-- Algebraic degree: sboxDegree^numRounds (naive upper bound). -/
def designAlgDegree (d : DesignParams) : Nat := d.sboxDegree ^ d.numRounds

/-- Total active S-boxes: branchNumber * numRounds (wide trail). -/
def designActiveSboxes (d : DesignParams) : Nat := d.branchNumber * d.numRounds

-- ============================================================
-- Monotonicity Theorems
-- ============================================================

/-- Algebraic degree is monotone in rounds (for degree ≥ 2). -/
theorem degree_mono_rounds (d : DesignParams) (extra : Nat)
    (hd : d.sboxDegree ≥ 2) :
    designAlgDegree d ≤
    designAlgDegree { d with numRounds := d.numRounds + extra,
                             h_rounds_pos := Nat.add_pos_left d.h_rounds_pos extra } := by
  simp [designAlgDegree]
  apply Nat.pow_le_pow_right
  · omega
  · omega

/-- Active S-boxes are monotone in rounds. -/
theorem active_sboxes_mono_rounds (d : DesignParams) (extra : Nat) :
    designActiveSboxes d ≤
    designActiveSboxes { d with numRounds := d.numRounds + extra,
                                h_rounds_pos := Nat.add_pos_left d.h_rounds_pos extra } := by
  simp [designActiveSboxes]
  apply Nat.mul_le_mul_left
  omega

/-- Active S-boxes are monotone in branch number. -/
theorem active_sboxes_mono_branch (d : DesignParams) (extra : Nat) :
    designActiveSboxes d ≤
    designActiveSboxes { d with branchNumber := d.branchNumber + extra } := by
  simp [designActiveSboxes]
  apply Nat.mul_le_mul_right
  omega

-- Smoke tests
private def testDesign : DesignParams where
  construction := .SPN
  stateWidth := 128
  sboxDegree := 7
  numRounds := 10
  branchNumber := 5

#eval designAlgDegree testDesign     -- 7^10 = 282475249
#eval designActiveSboxes testDesign  -- 5*10 = 50

end SuperHash
