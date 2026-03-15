/-!
# SuperHash.Security.QuantumBounds — Nat floor division bounds modeling quantum attack exponents

## Scope
Provides Nat floor division bounds that MODEL the exponents of quantum
query complexity (Grover, BHT). These are NOT proofs of quantum complexity
theory — they are verified arithmetic over natural numbers that captures
the floor-division relationships between classical and quantum security
parameters.

Specifically:
- `groverPreimageFloor n = n / 2` models the exponent reduction from
  Grover's algorithm (preimage: 2^n -> 2^{n/2} quantum queries)
- `bhtCollisionFloor n = n / 3` models the exponent reduction from
  BHT (collision: 2^{n/2} -> 2^{n/3} quantum queries)
- The theorems prove arithmetic relationships between these floor values
  (e.g., n/3 <= n/2, monotonicity, gap bounds)

## What these theorems prove
- Nat division inequalities: `n/3 <= n/2`, `n/3 <= n`, etc.
- Monotonicity: wider output -> higher quantum floor
- Gap bound: classical floor - quantum floor <= n/6 + 1
- Concrete evaluations: e.g., 128/3 = 42 for AES-128

## What these theorems do NOT prove
- Quantum query complexity lower bounds (require quantum information theory)
- Optimality of Grover/BHT algorithms
- Security of specific hash functions against quantum adversaries

## References
- Grover, "A fast quantum mechanical algorithm for database search" (1996)
- Brassard, Hoyer, Tapp, "Quantum Cryptanalysis of Hash Functions" (1998)
- Bernstein, "Cost analysis of hash collisions" (2009), §7
- Grassi et al., Poseidon(2)b (2025), §6.2 quantum considerations
-/

namespace SuperHash.Security.QuantumBounds

-- ============================================================
-- Section 1: Quantum floor definitions
-- ============================================================

/-- **Grover preimage floor: n/2 bits of quantum preimage security.**
    Grover's algorithm finds a preimage in O(2^{n/2}) quantum queries,
    reducing n-bit preimage resistance to n/2 bits.
    (Grover 1996; NIST post-quantum guidelines) -/
def groverPreimageFloor (n : Nat) : Nat := n / 2

/-- **BHT collision floor: n/3 bits of quantum collision security.**
    Brassard-Hoyer-Tapp algorithm finds collisions in O(2^{n/3}) quantum
    queries, reducing n/2-bit collision resistance to n/3 bits.
    (Brassard, Hoyer, Tapp 1998) -/
def bhtCollisionFloor (n : Nat) : Nat := n / 3

/-- **Quantum generic floor: minimum of all quantum generic bounds.**
    For collision resistance (the binding constraint), BHT gives n/3.
    This is the quantum-era replacement for the classical n/2 floor.
    (Bernstein 2009, §7) -/
def quantumGenericFloor (n : Nat) : Nat :=
  min (groverPreimageFloor n) (bhtCollisionFloor n)

/-- **Classical generic floor for reference.**
    n/2 bits of collision resistance from the birthday paradox. -/
def classicalGenericFloor (n : Nat) : Nat := n / 2

-- ============================================================
-- Section 2: Quantum bound theorems
-- ============================================================

/-- **BHT <= classical collision bound.**
    n/3 <= n/2 for all n. Quantum always at most as strong as classical.
    (BHT 1998; fundamental inequality) -/
theorem bht_le_classical (n : Nat) :
    bhtCollisionFloor n ≤ classicalGenericFloor n := by
  simp only [bhtCollisionFloor, classicalGenericFloor]; omega

/-- **Grover <= classical preimage.**
    n/2 <= n. Grover reduces preimage from n to n/2 bits.
    (Grover 1996) -/
theorem grover_le_classical_preimage (n : Nat) :
    groverPreimageFloor n ≤ n := by
  simp only [groverPreimageFloor]; omega

/-- **Quantum generic floor <= classical floor.**
    The quantum floor is always at most the classical floor.
    This is the binding constraint: deploying quantum computers
    can only reduce (never increase) the generic attack bound.
    (Bernstein 2009, §7) -/
theorem quantum_floor_le_classical (n : Nat) :
    quantumGenericFloor n ≤ classicalGenericFloor n := by
  simp only [quantumGenericFloor, classicalGenericFloor, groverPreimageFloor]
  exact Nat.min_le_left _ _

/-- **Quantum floor is monotone in output bits.**
    Wider output -> higher quantum security bound.
    (Structural: both n/2 and n/3 are monotone in n) -/
theorem quantum_floor_monotone (n₁ n₂ : Nat) (h : n₁ ≤ n₂) :
    quantumGenericFloor n₁ ≤ quantumGenericFloor n₂ := by
  simp only [quantumGenericFloor, groverPreimageFloor, bhtCollisionFloor]
  omega

/-- **Quantum floor positive for n >= 3.**
    n/3 >= 1 requires n >= 3.
    (Structural) -/
theorem quantum_floor_pos (n : Nat) (hn : n ≥ 3) :
    quantumGenericFloor n ≥ 1 := by
  simp only [quantumGenericFloor, groverPreimageFloor, bhtCollisionFloor]
  omega

/-- **Nat arithmetic: min(n/2, n/3) = n/3.**
    Since n/3 <= n/2 for all n (Nat floor division), the minimum
    of the two Grover/BHT floor values equals the BHT floor.
    This is a pure Nat division fact, not a quantum complexity proof. -/
theorem quantum_floor_eq_bht_collision (n : Nat) :
    quantumGenericFloor n = bhtCollisionFloor n := by
  simp only [quantumGenericFloor, groverPreimageFloor, bhtCollisionFloor]
  omega

/-- **Quantum gap: classical floor - quantum floor = n/2 - n/3 <= n/6 + 1.**
    The quantum advantage for collision finding is approximately n/6 bits.
    This quantifies how much quantum computers degrade collision security.
    (BHT 1998; Bernstein 2009, Table 1) -/
theorem quantum_gap_bound (n : Nat) :
    classicalGenericFloor n - quantumGenericFloor n ≤ n / 6 + 1 := by
  simp only [classicalGenericFloor, quantumGenericFloor, groverPreimageFloor,
             bhtCollisionFloor]
  omega

-- ============================================================
-- Section 3: Concrete instances
-- ============================================================

/-- **PRESENT-80: quantum collision floor = 26.**
    80/3 = 26. (vs classical 40) -/
theorem present80_quantum_floor :
    quantumGenericFloor 80 = 26 := by native_decide

/-- **AES-128: quantum collision floor = 42.**
    128/3 = 42. (vs classical 64) -/
theorem aes128_quantum_floor :
    quantumGenericFloor 128 = 42 := by native_decide

/-- **SHA-3-256: quantum collision floor = 85.**
    256/3 = 85. (vs classical 128) -/
theorem sha3_256_quantum_floor :
    quantumGenericFloor 256 = 85 := by native_decide

/-- **Poseidon-128: quantum collision floor = 42.**
    128/3 = 42. (vs classical 64) -/
theorem poseidon128_quantum_floor :
    quantumGenericFloor 128 = 42 := by native_decide

/-- **Rescue-Prime-128: quantum collision floor = 42.**
    128/3 = 42. (vs classical 64) -/
theorem rescue128_quantum_floor :
    quantumGenericFloor 128 = 42 := by native_decide

/-- **GMiMC-128: quantum collision floor = 42.**
    128/3 = 42. (vs classical 64) -/
theorem gmimc128_quantum_floor :
    quantumGenericFloor 128 = 42 := by native_decide

-- ============================================================
-- Section 4: Quantum rewrite rules
-- ============================================================

/-- **Nat arithmetic (E-graph rewrite form): quantumGenericFloor = bhtCollisionFloor.**
    Alias of `quantum_floor_eq_bht_collision` for use as an E-graph rewrite rule.
    Both sides compute to n/3. -/
theorem quantum_floor_eq_bht (n : Nat) :
    quantumGenericFloor n = bhtCollisionFloor n :=
  quantum_floor_eq_bht_collision n

/-- **Classical to quantum reduction factor.**
    classicalFloor n <= 2 * quantumGenericFloor n + 1.
    The classical floor is at most ~2x the quantum floor.
    (Structural: n/2 <= 2*(n/3) + 1) -/
theorem classical_le_double_quantum (n : Nat) :
    classicalGenericFloor n ≤ 2 * quantumGenericFloor n + 1 := by
  simp only [classicalGenericFloor, quantumGenericFloor, groverPreimageFloor,
             bhtCollisionFloor]
  omega

/-- **Quantum security monotone in structural cost.**
    If structural cost already dominates, quantum doesn't change verdict.
    min(qFloor, structCost) = qFloor when structCost >= qFloor.
    (Two-layer model) -/
theorem quantum_structural_dominates (n structCost : Nat)
    (h : structCost ≥ quantumGenericFloor n) :
    min (quantumGenericFloor n) structCost = quantumGenericFloor n := by
  omega

/-- **Classical floor always dominates quantum floor.**
    If result was min(classicalFloor, x), switching to min(quantumFloor, x)
    can only decrease or maintain the security level.
    (Upgrade path: quantum security level can only decrease) -/
theorem upgrade_security_nonincreasing (n x : Nat) :
    min (quantumGenericFloor n) x ≤ min (classicalGenericFloor n) x := by
  have h := quantum_floor_le_classical n
  omega

end SuperHash.Security.QuantumBounds
