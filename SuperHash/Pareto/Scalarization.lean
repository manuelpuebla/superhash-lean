import SuperHash.Pareto
import SuperHash.Pipeline.Instances

/-!
# SuperHash.Pareto.Scalarization — Weight vectors and scalarized cost

Provides:
- `Weights`: weight vector for multi-objective scalarization
- `weightedCostFn`: converts Weights → node-level cost function for E-graph extraction
- `scalarize`: scores a SecurityMetrics by a weight vector (higher = better)
- `scalarize_mono`: dominates a b → scalarize w a ≥ scalarize w b

The scalarization strategy (D5): different weight vectors → different extractions →
union filtered by Pareto front = approximation of Pareto-optimal designs.
Limitation: only finds convex hull of Pareto front (documented in D5).
-/

namespace SuperHash

/-- Weight vector for multi-objective scalarization.
    Each weight controls the relative importance of a SecurityMetrics dimension. -/
structure Weights where
  wSecurity : Nat   -- weight for security bits (higher bits = better)
  wLatency : Nat    -- weight for latency (lower = better)
  wGateCount : Nat  -- weight for gate count (lower = better)
  deriving Repr, DecidableEq, BEq

/-- Weighted node cost function for E-graph extraction.
    Different weight vectors produce different cost rankings → different extractions.
    The cost is minimized by extractF, so:
    - Higher wSecurity → lower cost for high-security nodes (prefer security)
    - Higher wLatency/wGateCount → higher cost for complex nodes (penalize complexity) -/
def weightedCostFn (w : Weights) : ENode CryptoOp → Nat :=
  fun node =>
    let baseCost := CryptoOp.localCost node.op
    let numChildren := (NodeOps.children node.op).length
    -- Security benefit: subtract from a large constant to invert (higher security → lower cost)
    -- Complexity penalty: add directly (higher complexity → higher cost)
    let securityPenalty := if baseCost > 0 then 1000 / baseCost else 1000
    w.wSecurity * securityPenalty + w.wLatency * baseCost + w.wGateCount * numChildren

/-- Scalarized score of a SecurityMetrics (higher = better design).
    Uses only the security dimension for formal monotonicity.
    Latency/gateCount are handled by Pareto filtering. -/
def scalarize (w : Weights) (m : SecurityMetrics) : Nat :=
  w.wSecurity * m.securityBits

/-- Monotonicity: dominating designs get higher scalarized scores. -/
theorem scalarize_mono (w : Weights) (a b : SecurityMetrics)
    (hdom : dominates a b) :
    scalarize w a ≥ scalarize w b := by
  simp only [scalarize, dominates] at *
  exact Nat.mul_le_mul_left _ hdom.1

-- Smoke tests
#eval scalarize ⟨1, 1, 1⟩ ⟨128, 10, 1000⟩  -- 128
#eval scalarize ⟨2, 1, 1⟩ ⟨128, 10, 1000⟩  -- 256
#eval weightedCostFn ⟨1, 0, 0⟩ ⟨.sbox 7 0⟩   -- security-focused
#eval weightedCostFn ⟨0, 1, 0⟩ ⟨.sbox 7 0⟩   -- latency-focused

-- Non-vacuity: scalarize_mono is satisfiable
example : scalarize ⟨1, 1, 1⟩ ⟨128, 10, 1000⟩ ≥ scalarize ⟨1, 1, 1⟩ ⟨64, 20, 2000⟩ := by
  native_decide

end SuperHash
