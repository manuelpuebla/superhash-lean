import SuperHash.Security.ThreatLattice4D
import SuperHash.Security.ActiveSboxBounds
import SuperHash.Security.QuantumBounds
import SuperHash.Security.DivisionProperty.CostModel
import SuperHash.Crypto.SecurityNotions
/-!
# SuperHash.Security.SecurityVerdict — Extended security verdict integration

## Scope
Bridges Phase 2 security components to SuperHash's existing SecurityProfile,
producing an `ExtendedVerdict` that combines:
- Classical collision/preimage bounds (from SecurityProfile)
- Quantum attack bounds (from QuantumBounds)
- Division property / integral attack bounds (from DivisionProperty.CostModel)
- Threat model context (from ThreatLattice4D)

## Key definitions
- `ExtendedVerdict`: unified struct for multi-dimensional security assessment
- `computeExtendedVerdict`: compute from design parameters
- `extendedVerdict_quantum_le_classical`: quantum floor constrains profile
- Concrete examples: AES-128, Poseidon-128, PRESENT-80

## References
- Rogaway-Shrimpton (2004): Rogaway-Shrimpton 7 security notions
- Brassard-Hoyer-Tapp (1998): quantum collision bounds
- Todo (2015): division property integral cryptanalysis
- Cheval et al. (2023): threat lattice model
-/

namespace SuperHash.Security.SecurityVerdict

open SuperHash (SecurityProfile)
open SuperHash.Security.ThreatLattice4D (ThreatModel rom mdRealistic spongeRealistic)
open SuperHash.Security.QuantumBounds
open SuperHash.Security.DivisionProperty.CostModel
open SuperHash.Security.DivisionProperty.Propagation
open SuperHash.Security.ActiveSboxBounds (ActiveSboxParams activeSboxCount)

-- ============================================================
-- Section 1: Design parameters
-- ============================================================

/-- **Design parameters for extended security verdict.**
    Captures the structural parameters needed to compute all security
    dimensions in one pass. -/
structure DesignParams where
  /-- Name of the hash function / permutation. -/
  name : String
  /-- Output size in bits. -/
  outputBits : Nat
  /-- Input size in bits (for division property). -/
  inputBits : Nat
  /-- S-box algebraic degree (for division property propagation). -/
  sboxDegree : Nat
  /-- Number of rounds in the cipher. -/
  rounds : Nat
  /-- Collision security bits (classical, from design analysis). -/
  classicalCollisionBits : Nat
  /-- Preimage security bits (classical). -/
  classicalPreimageBits : Nat
  /-- Threat model context. -/
  threatModel : ThreatModel
  deriving Repr

-- ============================================================
-- Section 2: Extended verdict structure
-- ============================================================

/-- **Extended security verdict**: combines classical, quantum, division
    property, and threat model assessments into a single structure.

    Each field represents a different dimension of security:
    - `classical`: Rogaway-Shrimpton security profile
    - `quantumCollisionFloor`: BHT collision bound (n/3 bits)
    - `quantumPreimageFloor`: Grover preimage bound (n/2 bits)
    - `divPropertyWeight`: remaining division weight after all rounds
    - `integralCost`: integral distinguisher cost in bits
    - `threatModel`: adversary capabilities assumed -/
structure ExtendedVerdict where
  classical              : SecurityProfile
  quantumCollisionFloor  : Nat
  quantumPreimageFloor   : Nat
  divPropertyWeight      : Nat
  integralCost           : Nat
  threatModel            : ThreatModel
  deriving Repr

-- ============================================================
-- Section 3: Verdict computation
-- ============================================================

/-- **Compute extended verdict from design parameters.**
    Assembles all security dimensions from a single DesignParams record:
    - Classical profile from stated collision/preimage bits
    - Quantum floors from output size
    - Division property from inputBits, sboxDegree, rounds
    - Integral cost from remaining division weight -/
def computeExtendedVerdict (dp : DesignParams) : ExtendedVerdict :=
  let qCollFloor := bhtCollisionFloor dp.outputBits
  let qPreFloor  := groverPreimageFloor dp.outputBits
  let divWeight  := divPropertyAfterRounds dp.inputBits dp.sboxDegree dp.rounds
  let intCost    := integralDistinguisherCost dp.outputBits divWeight
  { classical := {
      collisionBits      := dp.classicalCollisionBits
      preImageBits       := dp.classicalPreimageBits
      secondPreImageBits := dp.classicalPreimageBits
      targetCRBits       := dp.classicalPreimageBits
    }
    quantumCollisionFloor := qCollFloor
    quantumPreimageFloor  := qPreFloor
    divPropertyWeight     := divWeight
    integralCost          := intCost
    threatModel           := dp.threatModel }

-- ============================================================
-- Section 4: Structural theorems
-- ============================================================

/-- **Quantum collision floor ≤ classical collision bound.**
    The quantum BHT collision floor n/3 is always at most n/2 (birthday bound).
    Therefore quantum considerations can only tighten security.
    (BHT 1998; Bernstein 2009) -/
theorem extendedVerdict_quantum_le_classical (dp : DesignParams) :
    (computeExtendedVerdict dp).quantumCollisionFloor ≤
    dp.outputBits / 2 := by
  simp [computeExtendedVerdict]
  exact bht_le_classical dp.outputBits

/-- **Integral cost bounded by output bits.**
    The integral distinguisher cost from division property analysis
    never exceeds the output size.
    (Todo 2015, §6) -/
theorem extendedVerdict_integral_cost_le (dp : DesignParams) :
    (computeExtendedVerdict dp).integralCost ≤ dp.outputBits := by
  simp [computeExtendedVerdict]
  exact integral_cost_le_output _ _

/-- **Division property weight bounded by input bits.**
    After any number of rounds, the remaining weight is at most inputBits.
    (Structural: division weight is non-increasing through rounds) -/
theorem extendedVerdict_divWeight_le_input (dp : DesignParams)
    (hd : dp.sboxDegree ≥ 1) :
    (computeExtendedVerdict dp).divPropertyWeight ≤ dp.inputBits := by
  simp [computeExtendedVerdict]
  exact afterRounds_le_input dp.inputBits dp.sboxDegree hd dp.rounds

/-- **Quantum preimage floor ≤ classical preimage.**
    Grover reduces preimage from n to n/2 bits.
    (Grover 1996) -/
theorem extendedVerdict_grover_le (dp : DesignParams) :
    (computeExtendedVerdict dp).quantumPreimageFloor ≤
    dp.outputBits := by
  simp [computeExtendedVerdict]
  exact grover_le_classical_preimage dp.outputBits

/-- **Sufficient rounds → high integral cost.**
    If the division property is killed (weight ≤ 1), the integral cost
    is at least outputBits - 1, meaning the attack offers at most 1 bit
    of advantage.
    (Todo 2015, §6 + fixed-point preservation) -/
theorem sufficient_rounds_high_cost (dp : DesignParams)
    (hout : dp.outputBits ≥ 1)
    (hkill : divPropertyAfterRounds dp.inputBits dp.sboxDegree dp.rounds ≤ 1) :
    (computeExtendedVerdict dp).integralCost ≥ dp.outputBits - 1 := by
  simp only [computeExtendedVerdict]
  have := neutralized_weight_max_cost dp.outputBits _ hkill hout
  omega

-- ============================================================
-- Section 5: Concrete design parameters
-- ============================================================

/-- **AES-128 design parameters.** -/
def aes128Params : DesignParams where
  name := "AES-128"
  outputBits := 128
  inputBits := 128
  sboxDegree := 7
  rounds := 10
  classicalCollisionBits := 64
  classicalPreimageBits := 128
  threatModel := mdRealistic

/-- **Poseidon-128 design parameters.** -/
def poseidon128Params : DesignParams where
  name := "Poseidon-128"
  outputBits := 128
  inputBits := 128
  sboxDegree := 5
  rounds := 65
  classicalCollisionBits := 60
  classicalPreimageBits := 120
  threatModel := spongeRealistic

/-- **PRESENT-80 design parameters.** -/
def present80Params : DesignParams where
  name := "PRESENT-80"
  outputBits := 80
  inputBits := 80
  sboxDegree := 3
  rounds := 31
  classicalCollisionBits := 40
  classicalPreimageBits := 80
  threatModel := rom

-- ============================================================
-- Section 6: Concrete verdict examples
-- ============================================================

/-- **AES-128 extended verdict.** -/
def aes128Verdict : ExtendedVerdict := computeExtendedVerdict aes128Params

/-- **Poseidon-128 extended verdict.** -/
def poseidon128Verdict : ExtendedVerdict := computeExtendedVerdict poseidon128Params

/-- **PRESENT-80 extended verdict.** -/
def present80Verdict : ExtendedVerdict := computeExtendedVerdict present80Params

-- ============================================================
-- Section 7: Concrete theorem instances
-- ============================================================

/-- **AES-128 quantum collision floor = 42.**
    BHT gives 128/3 = 42 bits of quantum collision security.
    (vs classical 64 bits) -/
theorem aes128_verdict_quantum_coll :
    aes128Verdict.quantumCollisionFloor = 42 := by native_decide

/-- **AES-128 division property killed after 10 rounds.**
    Division weight ≤ 1 means no integral advantage. -/
theorem aes128_verdict_div_killed :
    aes128Verdict.divPropertyWeight ≤ 1 := by native_decide

/-- **AES-128 integral cost = 127 (near-full security).**
    With division weight = 1, integral cost = 128 - 1 = 127.
    Weight 1 is a fixed point of ⌈·/d⌉ for d ≥ 1. -/
theorem aes128_verdict_integral_cost :
    aes128Verdict.integralCost = 127 := by native_decide

/-- **Poseidon-128 quantum collision floor = 42.**
    Same output size as AES-128, same quantum floor. -/
theorem poseidon128_verdict_quantum_coll :
    poseidon128Verdict.quantumCollisionFloor = 42 := by native_decide

/-- **Poseidon-128 division property killed after 65 rounds.**
    Division weight ≤ 1 after 65 rounds with degree-5 S-box. -/
theorem poseidon128_verdict_div_killed :
    poseidon128Verdict.divPropertyWeight ≤ 1 := by native_decide

/-- **PRESENT-80 quantum collision floor = 26.**
    BHT gives 80/3 = 26 bits of quantum collision security.
    (vs classical 40 bits) -/
theorem present80_verdict_quantum_coll :
    present80Verdict.quantumCollisionFloor = 26 := by native_decide

/-- **PRESENT-80 division property killed after 31 rounds.**
    Division weight ≤ 1 after 31 rounds with degree-3 S-box. -/
theorem present80_verdict_div_killed :
    present80Verdict.divPropertyWeight ≤ 1 := by native_decide

-- ============================================================
-- Section 8: Non-vacuity examples
-- ============================================================

/-- **Non-vacuity 1: extendedVerdict_quantum_le_classical is satisfiable.**
    AES-128: quantumCollisionFloor (42) ≤ outputBits/2 (64). -/
example : (computeExtendedVerdict aes128Params).quantumCollisionFloor ≤
    aes128Params.outputBits / 2 :=
  extendedVerdict_quantum_le_classical aes128Params

/-- **Non-vacuity 2: sufficient_rounds_high_cost is satisfiable for AES.**
    AES-128: integral cost ≥ 127 (outputBits - 1). -/
example : (computeExtendedVerdict aes128Params).integralCost ≥
    aes128Params.outputBits - 1 :=
  sufficient_rounds_high_cost aes128Params (by native_decide) (by native_decide)

/-- **Non-vacuity 3: sufficient_rounds_high_cost is satisfiable for PRESENT.**
    PRESENT-80: integral cost ≥ 79 (outputBits - 1). -/
example : (computeExtendedVerdict present80Params).integralCost ≥
    present80Params.outputBits - 1 :=
  sufficient_rounds_high_cost present80Params (by native_decide) (by native_decide)

/-- **Non-vacuity 4: extendedVerdict_divWeight_le_input is satisfiable.**
    Poseidon-128: divPropertyWeight ≤ 128 (inputBits) with degree ≥ 1. -/
example : (computeExtendedVerdict poseidon128Params).divPropertyWeight ≤
    poseidon128Params.inputBits :=
  extendedVerdict_divWeight_le_input poseidon128Params (by native_decide)

end SuperHash.Security.SecurityVerdict
