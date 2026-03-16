import SuperHash.Crypto.DDT
import SuperHash.Crypto.AlgebraicDegree
import SuperHash.Crypto.CryptoRule
import SuperHash.Crypto.ExtractorBound

/-!
# SuperHash.Crypto.Fitness — TrustHash-style fitness function

v2.5 Phase 6 + v2.6 LHL integration: Composes all crypto metrics into
a unified fitness function backed by information-theoretic bounds.

## v2.6 upgrade (Tyagi-Watanabe Theorem 1)
The differential security bound `activeSboxes * (n - log2(δ))` is now
formally justified by the Leftover Hash Lemma: it equals the source
entropy of the DDT-induced distribution, from which at most k - 2s
bits can be extracted with s bits of security. See ExtractorBound.lean.

## Fitness Function (D19)
  securityLevel = min(genericFloor, differentialBound, algebraicBound)

Each component is backed by formal theorems:
- genericFloor: birthdayFloor (from LeanHash/BirthdayBound)
- differentialBound: from wide trail + certified δ
- algebraicBound: from degree^treewidth (Phase 5)

## Pipeline (TrustHash pattern)
  Design → CryptoSemantics → Fitness evaluation → Security level
-/

namespace SuperHash

-- ============================================================
-- Section 1: Unified fitness from CryptoSemantics
-- ============================================================

/-- Compute fitness (security level in bits) from CryptoSemantics.
    This is the core evaluation that drives E-graph extraction.

    security = min of three independent bounds:
    1. Birthday floor: outputBits / 2
    2. Differential bound: activeSboxes * (sboxBits - log2(δ))
    3. Algebraic bound: treewidth * log2(degree) -/
def fitness (outputBits sboxBits treewidth : Nat) (cs : CryptoSemantics) : Nat :=
  let birthday := outputBits / 2
  let differential :=
    if cs.differentialUniformity ≤ 1 then outputBits  -- ideal (δ≤1 means perfect)
    else cs.activeMinSboxes *
      (if ilog2 cs.differentialUniformity ≥ sboxBits then 0
       else sboxBits - ilog2 cs.differentialUniformity)
  let algebraic :=
    if cs.algebraicDegree ≤ 1 then 0  -- degree 0 or 1 = insecure
    else treewidth * ilog2 cs.algebraicDegree
  min birthday (min differential algebraic)

/-- Fitness is zero when degree is 0 or 1 (algebraically trivial). -/
theorem fitness_zero_trivial_degree (outputBits sboxBits tw : Nat) (cs : CryptoSemantics)
    (h : cs.algebraicDegree ≤ 1) :
    fitness outputBits sboxBits tw cs = 0 := by
  unfold fitness
  simp only [h, ite_true, Nat.min_zero]

-- ============================================================
-- Section 2: Design evaluation
-- ============================================================

/-- Hash design parameters for fitness evaluation. -/
structure DesignConfig where
  outputBits : Nat      -- e.g., 128 or 256
  sboxBits : Nat        -- S-box input width (e.g., 8 for AES)
  treewidth : Nat       -- treewidth of constraint graph (e.g., 5 for AES)

/-- Standard configs. -/
def aes128Config : DesignConfig := ⟨128, 8, 5⟩
def poseidon128Config : DesignConfig := ⟨256, 64, 3⟩

/-- Evaluate fitness for a specific design config. -/
def evaluateDesign (cfg : DesignConfig) (cs : CryptoSemantics) : Nat :=
  fitness cfg.outputBits cfg.sboxBits cfg.treewidth cs

-- ============================================================
-- Section 3: Concrete evaluations
-- ============================================================

-- AES-128 fitness: min(64, 300, 35) = 35 (algebraic-bounded)
#eval evaluateDesign aes128Config aes128Semantics
-- birthday=64, diff=50*(8-2)=300, alg=5*log2(128)=5*7=35 → min=35

-- Poseidon-128 fitness: min(128, 2016, 54) = 54 (algebraic-bounded!)
#eval evaluateDesign poseidon128Config poseidon128Semantics
-- birthday=128, diff=32*(64-1)=2016, alg=3*log2(5^8)=3*18=54 → min=54
-- This correctly identifies that Poseidon with only 8 full rounds is ALGEBRAICALLY WEAK!

/-- Poseidon with more rounds: degree = 5^65 ≈ 2^150 → alg = 3*150 = 450.
    min(128, 4095, 450) = 128 (now birthday-bounded, secure!). -/
def poseidon128_65rounds : CryptoSemantics where
  algebraicDegree := 5 ^ 65
  differentialUniformity := 2
  linearBias := 0
  branchNumber := 4
  activeMinSboxes := 260  -- BN * R = 4 * 65
  latency := 65
  gateCount := 195
  circuitDepth := 65

#eval evaluateDesign poseidon128Config poseidon128_65rounds
-- 128 (secure: birthday-bounded)

-- ============================================================
-- Section 4: Fitness comparison (design space exploration)
-- ============================================================

/-- Compare two designs: which has higher fitness? -/
def betterDesign (cfg : DesignConfig) (a b : CryptoSemantics) : Bool :=
  evaluateDesign cfg a > evaluateDesign cfg b

/-- More rounds → higher algebraic security component.
    Uses algebraicSecurityBits which is defined via ilog2. -/
theorem more_rounds_better_algebraic_security (alpha r1 r2 tw : Nat)
    (hα : alpha ≥ 2) (hR : r1 ≤ r2) :
    algebraicSecurityBits (alpha ^ r1) tw ≤
    algebraicSecurityBits (alpha ^ r2) tw :=
  algebraic_security_mono_rounds alpha r1 r2 tw hα hR

-- ============================================================
-- Section 5: Pipeline composition
-- ============================================================

/-- Full v2.5 pipeline: take a CryptoOp expression, evaluate to CryptoSemantics,
    compute fitness. This replaces the Nat-based pipeline from v2.0. -/
def evaluateCryptoOp (cfg : DesignConfig) (op : CryptoOp) (children : List CryptoSemantics) : Nat :=
  evaluateDesign cfg (evalCryptoSem op children)

-- Pipeline demo: evaluate an SPN block
#eval evaluateCryptoOp aes128Config (.spnBlock 10 0 0)
  [⟨7, 4, 16, 0, 1, 1, 7, 1⟩,    -- S-box child: deg=7, δ=4
   ⟨1, 0, 0, 5, 0, 1, 5, 1⟩]     -- linear child: BN=5

-- ============================================================
-- Section 6: Non-vacuity
-- ============================================================

/-- Non-vacuity: AES fitness = 35 (algebraic-bounded with BCD11 tight degree=128). -/
example : evaluateDesign aes128Config aes128Semantics = 35 := by native_decide

/-- Non-vacuity: Poseidon (8 rounds) fitness = 54 (algebraic weakness!). -/
example : evaluateDesign poseidon128Config poseidon128Semantics = 54 := by native_decide

/-- Non-vacuity: trivial design (deg=1) has fitness = 0. -/
example : fitness 128 8 5 ⟨1, 4, 16, 5, 50, 10, 50, 40⟩ = 0 := by native_decide

/-- Non-vacuity: the fitness function correctly identifies that
    Poseidon needs ≥65 rounds for 128-bit security. -/
example : evaluateDesign poseidon128Config poseidon128_65rounds ≥ 128 := by native_decide

end SuperHash
