import SuperHash.Pareto.ExtendedExtract
import SuperHash.Crypto.SecurityNotions
import SuperHash.Pipeline.MasterTheoremCS

/-!
# SuperHash.Pareto.PipelineBridge — Bridge from pipeline to 6D Pareto

Connects the SuperHash pipeline output to ExtendedSecurityMetrics:
- `cryptoSemanticsToExtended` : CryptoSemantics → ExtendedSecurityMetrics
  using cryptoSemanticsToProfile for security + CryptoSemantics for efficiency
- Bridge theorems ensuring the projection to 3D SecurityMetrics is consistent
- Concrete instances for AES-128, Poseidon-128, SHA-256

The key insight: CryptoSemantics already carries latency and gateCount,
and cryptoSemanticsToProfile computes the 4 security dimensions. This
bridge simply combines both into the unified 6D representation.
-/

namespace SuperHash

-- ============================================================
-- Section 1: Core bridge function
-- ============================================================

/-- **Convert CryptoSemantics to ExtendedSecurityMetrics.**
    Security dimensions come from cryptoSemanticsToProfile (Rogaway-Shrimpton).
    Efficiency dimensions come directly from CryptoSemantics.

    Parameters:
    - `cs` : CryptoSemantics with all 7 cryptographic metrics
    - `sboxBits` : S-box input width (e.g., 8 for AES)
    - `outputBits` : hash output size in bits -/
def cryptoSemanticsToExtended (cs : CryptoSemantics) (sboxBits outputBits : Nat) :
    ExtendedSecurityMetrics :=
  let profile := cryptoSemanticsToProfile cs sboxBits outputBits
  { collisionBits      := profile.collisionBits
    preImageBits       := profile.preImageBits
    secondPreImageBits := profile.secondPreImageBits
    targetCRBits       := profile.targetCRBits
    latency            := cs.latency
    gateCount          := cs.gateCount }

-- ============================================================
-- Section 2: Bridge theorems
-- ============================================================

/-- Bridge factors through fromProfileAndMetrics. -/
theorem cryptoSemanticsToExtended_eq (cs : CryptoSemantics) (sboxBits outputBits : Nat) :
    cryptoSemanticsToExtended cs sboxBits outputBits =
    fromProfileAndMetrics (cryptoSemanticsToProfile cs sboxBits outputBits)
                          ⟨0, cs.latency, cs.gateCount⟩ := by
  simp [cryptoSemanticsToExtended, fromProfileAndMetrics]

/-- **Projection to 3D SecurityMetrics preserves weak ordering.**
    If cryptoSemanticsToExtended a ext-dominates b, then the 3D projections
    maintain all-dimensions-at-least-as-good. -/
theorem extended_projection_sound (a b : CryptoSemantics)
    (sboxBitsA sboxBitsB outputBitsA outputBitsB : Nat)
    (hdom : extDominates (cryptoSemanticsToExtended a sboxBitsA outputBitsA)
                         (cryptoSemanticsToExtended b sboxBitsB outputBitsB)) :
    (toSecurityMetrics (cryptoSemanticsToExtended a sboxBitsA outputBitsA)).securityBits ≥
    (toSecurityMetrics (cryptoSemanticsToExtended b sboxBitsB outputBitsB)).securityBits ∧
    (toSecurityMetrics (cryptoSemanticsToExtended a sboxBitsA outputBitsA)).latency ≤
    (toSecurityMetrics (cryptoSemanticsToExtended b sboxBitsB outputBitsB)).latency ∧
    (toSecurityMetrics (cryptoSemanticsToExtended a sboxBitsA outputBitsA)).gateCount ≤
    (toSecurityMetrics (cryptoSemanticsToExtended b sboxBitsB outputBitsB)).gateCount :=
  extDominates_implies_weak_dominates _ _ hdom

/-- **6D ext-dominance with efficiency improvement gives full 3D dominance.** -/
theorem extended_projection_dominates (a b : CryptoSemantics)
    (sboxBitsA sboxBitsB outputBitsA outputBitsB : Nat)
    (hdom : extDominates (cryptoSemanticsToExtended a sboxBitsA outputBitsA)
                         (cryptoSemanticsToExtended b sboxBitsB outputBitsB))
    (heff : (cryptoSemanticsToExtended a sboxBitsA outputBitsA).latency <
            (cryptoSemanticsToExtended b sboxBitsB outputBitsB).latency ∨
            (cryptoSemanticsToExtended a sboxBitsA outputBitsA).gateCount <
            (cryptoSemanticsToExtended b sboxBitsB outputBitsB).gateCount) :
    dominates (toSecurityMetrics (cryptoSemanticsToExtended a sboxBitsA outputBitsA))
              (toSecurityMetrics (cryptoSemanticsToExtended b sboxBitsB outputBitsB)) :=
  extDominates_efficiency_implies_dominates _ _ hdom heff

/-- **Extended metrics preserve collision bits from profile.** -/
theorem extended_collision_eq_profile (cs : CryptoSemantics) (sboxBits outputBits : Nat) :
    (cryptoSemanticsToExtended cs sboxBits outputBits).collisionBits =
    (cryptoSemanticsToProfile cs sboxBits outputBits).collisionBits := rfl

/-- **Extended metrics preserve preimage bits from profile.** -/
theorem extended_preImage_eq_profile (cs : CryptoSemantics) (sboxBits outputBits : Nat) :
    (cryptoSemanticsToExtended cs sboxBits outputBits).preImageBits =
    (cryptoSemanticsToProfile cs sboxBits outputBits).preImageBits := rfl

/-- **Extended metrics preserve latency from CryptoSemantics.** -/
theorem extended_latency_eq (cs : CryptoSemantics) (sboxBits outputBits : Nat) :
    (cryptoSemanticsToExtended cs sboxBits outputBits).latency = cs.latency := rfl

/-- **Extended metrics preserve gateCount from CryptoSemantics.** -/
theorem extended_gateCount_eq (cs : CryptoSemantics) (sboxBits outputBits : Nat) :
    (cryptoSemanticsToExtended cs sboxBits outputBits).gateCount = cs.gateCount := rfl

/-- **Extended profile is ideal-bounded (inherited from cryptoSemanticsToProfile).** -/
theorem extended_ideal_bounded (cs : CryptoSemantics) (sboxBits n : Nat) :
    isIdealBounded (cryptoSemanticsToProfile cs sboxBits n) n :=
  bridge_is_ideal_bounded cs sboxBits n

-- ============================================================
-- Section 3: Concrete instances
-- ============================================================

/-- AES-128 extended metrics from CryptoSemantics.
    sboxBits=8, outputBits=128. -/
def aes128ExtendedFromCS : ExtendedSecurityMetrics :=
  cryptoSemanticsToExtended aes128Semantics 8 128

/-- Poseidon-128 extended metrics from CryptoSemantics.
    sboxBits=64, outputBits=256. -/
def poseidon128ExtendedFromCS : ExtendedSecurityMetrics :=
  cryptoSemanticsToExtended poseidon128Semantics 64 256

/-- SHA-256 extended metrics (manual, as SHA-256 does not have a CryptoSemantics instance).
    Uses sha256Profile security + realistic efficiency estimates. -/
def sha256ExtendedFromProfile : ExtendedSecurityMetrics :=
  fromProfileAndMetrics sha256Profile ⟨0, 64, 200⟩

-- ============================================================
-- Section 4: Concrete validation
-- ============================================================

/-- AES-128 collision bits from pipeline = 28 (min of birthday, differential, algebraic). -/
theorem aes128_extended_collision :
    aes128ExtendedFromCS.collisionBits = 28 := by native_decide

/-- AES-128 latency preserved from CryptoSemantics. -/
theorem aes128_extended_latency :
    aes128ExtendedFromCS.latency = 10 := by native_decide

/-- Poseidon-128 collision bits from pipeline = 18. -/
theorem poseidon128_extended_collision :
    poseidon128ExtendedFromCS.collisionBits = 18 := by native_decide

/-- SHA-256 extended from profile gives 128 collision bits. -/
theorem sha256_extended_collision :
    sha256ExtendedFromProfile.collisionBits = 128 := by native_decide

/-- SHA-256 extended latency. -/
theorem sha256_extended_latency :
    sha256ExtendedFromProfile.latency = 64 := by native_decide

-- ============================================================
-- Section 5: Non-vacuity examples
-- ============================================================

/-- Non-vacuity 1: cryptoSemanticsToExtended produces concrete values. -/
example : (cryptoSemanticsToExtended aes128Semantics 8 128).collisionBits = 28 := by
  native_decide

/-- Non-vacuity 2: Poseidon extended metrics are concrete. -/
example : (cryptoSemanticsToExtended poseidon128Semantics 64 256).collisionBits = 18 := by
  native_decide

/-- Non-vacuity 3: 3D projection of pipeline designs has correct securityBits. -/
example : (toSecurityMetrics sha256ExtendedFromProfile).securityBits = 128 := by
  native_decide

/-- Non-vacuity 4: extended ideal bounded for AES-128. -/
example : isIdealBounded (cryptoSemanticsToProfile aes128Semantics 8 128) 128 :=
  extended_ideal_bounded aes128Semantics 8 128

/-- Non-vacuity 5: Pareto front of extended metrics from pipeline. -/
example : (extParetoFront [aes128ExtendedFromCS, poseidon128ExtendedFromCS,
                           sha256ExtendedFromProfile]).length ≤ 3 := by
  native_decide

-- Smoke tests
#eval aes128ExtendedFromCS
#eval poseidon128ExtendedFromCS
#eval sha256ExtendedFromProfile
#eval toSecurityMetrics aes128ExtendedFromCS
#eval extParetoFront [aes128ExtendedFromCS, poseidon128ExtendedFromCS, sha256ExtendedFromProfile]

end SuperHash
