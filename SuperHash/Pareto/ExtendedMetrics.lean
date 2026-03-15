import SuperHash.Pareto
import SuperHash.Crypto.SecurityNotions

/-!
# SuperHash.Pareto.ExtendedMetrics — 6-dimensional security metrics

Extends the 3D SecurityMetrics (securityBits, latency, gateCount) to a 6D
representation that captures all four Rogaway-Shrimpton security notions
(collisionBits, preImageBits, secondPreImageBits, targetCRBits) plus
efficiency dimensions (latency, gateCount).

Bridges:
- `toSecurityMetrics` : project to 3D (min of 4 security dims → securityBits)
- `fromProfileAndMetrics` : combine SecurityProfile + SecurityMetrics → 6D

Adapted from LeanHash.DesignSpace extended metrics.
-/

namespace SuperHash

-- ============================================================
-- Section 1: Extended Security Metrics
-- ============================================================

/-- **6-dimensional security metrics.**
    Four security dimensions from Rogaway-Shrimpton (2004) + two efficiency
    dimensions. Generalizes SecurityMetrics from 3D to 6D for richer Pareto
    analysis over the full security surface. -/
structure ExtendedSecurityMetrics where
  collisionBits      : Nat  -- Coll (↑ better)
  preImageBits       : Nat  -- Pre  (↑ better)
  secondPreImageBits : Nat  -- Sec  (↑ better)
  targetCRBits       : Nat  -- eSec (↑ better)
  latency            : Nat  -- (↓ better)
  gateCount          : Nat  -- (↓ better)
  deriving Repr, DecidableEq, BEq

-- ============================================================
-- Section 2: Bridges
-- ============================================================

/-- **Project to 3D SecurityMetrics.**
    Maps the minimum of the 4 security dimensions to securityBits.
    This is conservative: a design is only as strong as its weakest notion. -/
def toSecurityMetrics (e : ExtendedSecurityMetrics) : SecurityMetrics where
  securityBits := min e.collisionBits (min e.preImageBits
                    (min e.secondPreImageBits e.targetCRBits))
  latency := e.latency
  gateCount := e.gateCount

/-- **Lift from SecurityProfile + SecurityMetrics to 6D.**
    Takes security dimensions from the profile and efficiency from metrics. -/
def fromProfileAndMetrics (sp : SecurityProfile) (sm : SecurityMetrics) :
    ExtendedSecurityMetrics where
  collisionBits      := sp.collisionBits
  preImageBits       := sp.preImageBits
  secondPreImageBits := sp.secondPreImageBits
  targetCRBits       := sp.targetCRBits
  latency            := sm.latency
  gateCount          := sm.gateCount

-- ============================================================
-- Section 3: Bridge theorems
-- ============================================================

/-- Projection preserves latency. -/
theorem toSecurityMetrics_latency (e : ExtendedSecurityMetrics) :
    (toSecurityMetrics e).latency = e.latency := rfl

/-- Projection preserves gateCount. -/
theorem toSecurityMetrics_gateCount (e : ExtendedSecurityMetrics) :
    (toSecurityMetrics e).gateCount = e.gateCount := rfl

/-- Projection securityBits ≤ collisionBits. -/
theorem toSecurityMetrics_le_collision (e : ExtendedSecurityMetrics) :
    (toSecurityMetrics e).securityBits ≤ e.collisionBits := by
  simp [toSecurityMetrics]
  exact Nat.min_le_left _ _

/-- Roundtrip: fromProfileAndMetrics preserves all SecurityProfile fields. -/
theorem fromProfileAndMetrics_collision (sp : SecurityProfile) (sm : SecurityMetrics) :
    (fromProfileAndMetrics sp sm).collisionBits = sp.collisionBits := rfl

theorem fromProfileAndMetrics_preImage (sp : SecurityProfile) (sm : SecurityMetrics) :
    (fromProfileAndMetrics sp sm).preImageBits = sp.preImageBits := rfl

theorem fromProfileAndMetrics_secondPreImage (sp : SecurityProfile) (sm : SecurityMetrics) :
    (fromProfileAndMetrics sp sm).secondPreImageBits = sp.secondPreImageBits := rfl

theorem fromProfileAndMetrics_targetCR (sp : SecurityProfile) (sm : SecurityMetrics) :
    (fromProfileAndMetrics sp sm).targetCRBits = sp.targetCRBits := rfl

-- ============================================================
-- Section 4: Concrete instances
-- ============================================================

/-- AES-128 extended metrics: Coll=64, Pre=Sec=eSec=128, lat=10, gates=50. -/
def aes128Extended : ExtendedSecurityMetrics where
  collisionBits      := 64
  preImageBits       := 128
  secondPreImageBits := 128
  targetCRBits       := 128
  latency            := 10
  gateCount          := 50

/-- Poseidon-128 extended metrics: Coll=60, Pre=Sec=eSec=120, lat=8, gates=24. -/
def poseidon128Extended : ExtendedSecurityMetrics where
  collisionBits      := 60
  preImageBits       := 120
  secondPreImageBits := 120
  targetCRBits       := 120
  latency            := 8
  gateCount          := 24

/-- SHA-256 extended metrics: Coll=128, Pre=Sec=eSec=256, lat=64, gates=200. -/
def sha256Extended : ExtendedSecurityMetrics where
  collisionBits      := 128
  preImageBits       := 256
  secondPreImageBits := 256
  targetCRBits       := 256
  latency            := 64
  gateCount          := 200

-- ============================================================
-- Section 5: Non-vacuity examples
-- ============================================================

/-- Non-vacuity 1: ExtendedSecurityMetrics is inhabited. -/
example : ExtendedSecurityMetrics := aes128Extended

/-- Non-vacuity 2: toSecurityMetrics produces sensible values for AES-128. -/
example : (toSecurityMetrics aes128Extended).securityBits = 64 := by native_decide

/-- Non-vacuity 3: toSecurityMetrics produces sensible values for Poseidon-128. -/
example : (toSecurityMetrics poseidon128Extended).securityBits = 60 := by native_decide

/-- Non-vacuity 4: fromProfileAndMetrics roundtrips correctly. -/
example : fromProfileAndMetrics aes128Profile ⟨64, 10, 50⟩ = aes128Extended := by
  native_decide

/-- Non-vacuity 5: SHA-256 has higher collision bits than AES-128 extended. -/
example : sha256Extended.collisionBits > aes128Extended.collisionBits := by native_decide

-- Smoke tests
#eval toSecurityMetrics aes128Extended
#eval toSecurityMetrics poseidon128Extended
#eval toSecurityMetrics sha256Extended

end SuperHash
