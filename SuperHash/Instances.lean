import SuperHash.DesignParams
import SuperHash.Pareto

/-!
# SuperHash.Instances — Concrete hash design instances

AES-128 and Poseidon-128 design parameters with verified properties.
Adapted from LeanHash.DesignSpace.
-/

namespace SuperHash

/-- AES-128 design parameters.
    SPN, 16-byte state, x^254 S-box (degree 7), 10 rounds, branch 5. -/
def aes128Design : DesignParams where
  construction := .SPN
  stateWidth := 16
  sboxDegree := 7
  numRounds := 10
  branchNumber := 5

/-- AES-128 algebraic degree = 7^10. -/
theorem aes128_alg_degree : designAlgDegree aes128Design = 7 ^ 10 := rfl

/-- AES-128 active S-boxes = 50. -/
theorem aes128_active_sboxes : designActiveSboxes aes128Design = 50 := by
  native_decide

/-- AES-128 degree exceeds 2^28. -/
theorem aes128_degree_exceeds : designAlgDegree aes128Design ≥ 2 ^ 28 := by
  native_decide

/-- Poseidon-128 design parameters (full rounds).
    SPN, 3-element state, x^5 S-box, 8 full rounds, branch 4. -/
def poseidon128Design : DesignParams where
  construction := .SPN
  stateWidth := 3
  sboxDegree := 5
  numRounds := 8
  branchNumber := 4

/-- Poseidon-128 algebraic degree = 5^8. -/
theorem poseidon128_alg_degree : designAlgDegree poseidon128Design = 5 ^ 8 := rfl

/-- Poseidon-128 active S-boxes = 32. -/
theorem poseidon128_active_sboxes : designActiveSboxes poseidon128Design = 32 := by
  native_decide

/-- Poseidon-128 degree exceeds 2^18. -/
theorem poseidon128_degree_exceeds : designAlgDegree poseidon128Design ≥ 2 ^ 18 := by
  native_decide

/-- AES-128 metrics (representative): fast but large circuit. -/
def aes128Metrics : SecurityMetrics where
  securityBits := 128
  latency := 40
  gateCount := 30000

/-- Poseidon-128 metrics (representative): slower but small circuit. -/
def poseidon128Metrics : SecurityMetrics where
  securityBits := 128
  latency := 50
  gateCount := 8000

/-- Neither AES nor Poseidon dominates the other (different trade-offs).
    AES has lower latency, Poseidon has lower gate count. -/
theorem aes_poseidon_incomparable :
    ¬ dominates aes128Metrics poseidon128Metrics ∧
    ¬ dominates poseidon128Metrics aes128Metrics := by
  constructor
  · intro ⟨_, _, h3, _⟩; simp [aes128Metrics, poseidon128Metrics] at h3
  · intro ⟨_, h2, _, _⟩; simp [aes128Metrics, poseidon128Metrics] at h2

-- Smoke
#eval paretoFront [aes128Metrics, poseidon128Metrics]
-- Both should survive (incomparable)

end SuperHash
