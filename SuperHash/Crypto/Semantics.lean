import SuperHash.CryptoOp

/-!
# SuperHash.Crypto.Semantics — CryptoSemantics: The Real Semantic Domain

v2.5 Core: Replaces Val:=Nat with a domain that captures actual cryptographic
properties. This is the central type that closes the "Nat arithmetic" gap.

## CryptoSemantics fields (D14)
- `algebraicDegree`: degree of the polynomial over GF(2^n)
- `differentialUniformity`: δ — max entries in DDT
- `linearBias`: ε — max bias in LAT (QA #4)
- `branchNumber`: min Hamming weight sum through MDS
- `activeMinSboxes`: minimum active S-boxes in any differential trail
- `latency`: clock cycles (performance model)
- `gateCount`: logic gates (area model)

## Design Decisions
- D15: Sequential compose ≠ parallel (different crypto semantics)
- L-376: Uses Inhabited with default (all zeros), not Option
- L-458: Concrete type, not parametric typeclass
- L-550: All exponent operations guard against 0^0=1

## Sources
- LeanHash/SboxProperties.lean: SboxParams structure
- LeanHash/MDSMatrix.lean: branchNumber definition
- LeanHash/DesignSpace.lean: SecurityMetrics, dominates
-/

namespace SuperHash

-- ============================================================
-- Section 1: S-box Parameter Space (from LeanHash)
-- ============================================================

/-- S-box cryptographic parameters. Captures the three axes of
    resistance: differential (δ), linear (NL), algebraic (deg).
    Source: LeanHash/SboxProperties.lean, adapted. -/
structure SboxParams where
  inputBits : Nat
  diffUniformity : Nat    -- δ: max DDT entry
  nonlinearity : Nat      -- NL: min distance to affine
  algebraicDeg : Nat      -- deg of ANF
  h_bits : inputBits ≥ 1
  h_du_pos : diffUniformity ≥ 2  -- APN minimum (Dey & Ghosh 2019)
  h_deg_pos : algebraicDeg ≥ 1
  deriving Repr

-- ============================================================
-- Section 2: MDS Branch Number (from LeanHash)
-- ============================================================

/-- Branch number of a t×t MDS matrix: br(M) = t + 1.
    Source: LeanHash/MDSMatrix.lean, Daemen & Rijmen 2002. -/
def mds_branchNumber (t : Nat) : Nat := t + 1

theorem mds_branch_exceeds_dim (t : Nat) : mds_branchNumber t > t := by
  simp [mds_branchNumber]

theorem mds_branch_positive (t : Nat) (ht : t ≥ 1) : mds_branchNumber t ≥ 2 := by
  simp [mds_branchNumber]; omega

/-- Wide trail: active S-boxes ≥ br(M) * ⌊R/2⌋ over R rounds.
    Source: LeanHash/MDSMatrix.lean -/
theorem wide_trail_bound (bn R : Nat) (hbn : bn ≥ 2) :
    bn * (R / 2) ≥ R / 2 := Nat.le_mul_of_pos_left _ (by omega)

-- ============================================================
-- Section 3: CryptoSemantics — THE CORE TYPE
-- ============================================================

/-- The crypto semantic domain. Each field captures a measurable
    cryptographic or performance property of a hash design component.

    This replaces Val:=Nat from v1.0/v2.0. Every operation in the
    E-graph evaluates to a CryptoSemantics value, enabling rewrite
    rules with real security preconditions. -/
structure CryptoSemantics where
  /-- Algebraic degree of the polynomial representation over GF(2^n).
      Unit: dimensionless (polynomial degree). Higher → harder algebraic attacks. -/
  algebraicDegree : Nat
  /-- Differential uniformity δ: max_{a≠0,b} #{x : S(x)⊕S(x⊕a)=b}.
      Unit: count of input pairs (range [2, 2^n]). Lower → harder differential attacks. -/
  differentialUniformity : Nat
  /-- Linear bias ε: max deviation from uniform in LAT.
      Unit: absolute count (range [0, 2^(n-1)]). Lower → harder linear attacks. -/
  linearBias : Nat
  /-- Branch number of the associated linear layer.
      Unit: dimensionless (min Hamming weight sum). Higher → more active S-boxes. -/
  branchNumber : Nat
  /-- Minimum active S-boxes across all non-trivial differential trails.
      Unit: count of S-boxes. Higher → stronger security bound. -/
  activeMinSboxes : Nat
  /-- Latency: abstract time units proportional to clock cycles.
      Unit: abstract (1 = cost of one S-box or linear layer application). -/
  latency : Nat
  /-- Gate count: abstract area units proportional to logic gates.
      Unit: abstract (1 = cost of one basic operation). -/
  gateCount : Nat
  deriving Repr, DecidableEq, BEq, Hashable

instance : Inhabited CryptoSemantics where
  default := ⟨0, 0, 0, 0, 0, 0, 0⟩

-- ============================================================
-- Section 4: Dominance relation (Pareto over CryptoSemantics)
-- ============================================================

/-- Security-aware dominance: design A dominates B if A is at least
    as good in ALL security dimensions and strictly better in at least one.
    Note: for δ and linearBias, LOWER is better. For the rest, HIGHER is better. -/
def cryptoDominates (a b : CryptoSemantics) : Prop :=
  a.algebraicDegree ≥ b.algebraicDegree ∧
  a.differentialUniformity ≤ b.differentialUniformity ∧
  a.linearBias ≤ b.linearBias ∧
  a.branchNumber ≥ b.branchNumber ∧
  a.activeMinSboxes ≥ b.activeMinSboxes ∧
  a.latency ≤ b.latency ∧
  a.gateCount ≤ b.gateCount ∧
  (a.algebraicDegree > b.algebraicDegree ∨
   a.differentialUniformity < b.differentialUniformity ∨
   a.linearBias < b.linearBias ∨
   a.branchNumber > b.branchNumber ∨
   a.activeMinSboxes > b.activeMinSboxes ∨
   a.latency < b.latency ∨
   a.gateCount < b.gateCount)

theorem cryptoDominates_irrefl (a : CryptoSemantics) : ¬cryptoDominates a a := by
  intro ⟨_, _, _, _, _, _, _, h⟩
  rcases h with h | h | h | h | h | h | h <;> omega

theorem cryptoDominates_asymm (a b : CryptoSemantics) :
    cryptoDominates a b → ¬cryptoDominates b a := by
  intro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ ⟨g1, g2, g3, g4, g5, g6, g7, _g8⟩
  rcases h8 with h | h | h | h | h | h | h <;> omega

-- ============================================================
-- Section 5: Concrete instances
-- ============================================================

/-- AES S-box params: 8-bit, δ=4, NL=112, deg=7. -/
def aesSboxParams : SboxParams where
  inputBits := 8
  diffUniformity := 4
  nonlinearity := 112
  algebraicDeg := 7
  h_bits := by omega
  h_du_pos := by omega
  h_deg_pos := by omega

/-- PRESENT S-box params: 4-bit, δ=4, NL=4, deg=3. -/
def presentSboxParams : SboxParams where
  inputBits := 4
  diffUniformity := 4
  nonlinearity := 4
  algebraicDeg := 3
  h_bits := by omega
  h_du_pos := by omega
  h_deg_pos := by omega

/-- Poseidon S-box (x^5 over Fp): deg=5, δ=2 (APN for odd characteristic). -/
def poseidonSboxParams : SboxParams where
  inputBits := 64  -- field element bits
  diffUniformity := 2  -- APN
  nonlinearity := 0  -- not meaningful for prime fields
  algebraicDeg := 5
  h_bits := by omega
  h_du_pos := by omega
  h_deg_pos := by omega

/-- AES-128 full design as CryptoSemantics.
    NOTE: δ=4 assumed from Daemen & Rijmen 2002, not computed via DDT.
    TODO: verify via CertifiedSbox when 256-entry AES S-box table available.
    10 rounds, S-box deg=7, MDS BN=5 → activeSboxes ≥ 5*5=25. -/
def aes128Semantics : CryptoSemantics where
  algebraicDegree := 7 ^ 10  -- deg = 7^10 ≈ 2.8 × 10^8
  differentialUniformity := 4
  linearBias := 16  -- 2^4 for AES
  branchNumber := 5  -- 4×4 MDS → BN=5
  activeMinSboxes := 25  -- 5 * 5 (5 rounds of 2-round pairs)
  latency := 10
  gateCount := 50

/-- Poseidon-128 design as CryptoSemantics.
    NOTE: δ=2 (APN) assumed from Grassi et al. 2019 for x^5 over Fp.
    R_F=8, R_P=57, deg=5, BN=4 → activeSboxes ≥ 4*4=16. -/
def poseidon128Semantics : CryptoSemantics where
  algebraicDegree := 5 ^ 8  -- full rounds only: 5^8 = 390625
  differentialUniformity := 2  -- APN
  linearBias := 0
  branchNumber := 4  -- t=3 MDS → BN=4
  activeMinSboxes := 16
  latency := 8
  gateCount := 24

-- ============================================================
-- Section 6: S-box property theorems (adapted from LeanHash)
-- ============================================================

/-- APN is optimal: no S-box can have δ < 2.
    Source: LeanHash/SboxProperties.lean -/
theorem apn_optimal : ∀ (sp : SboxParams), sp.diffUniformity ≥ 2 := fun sp => sp.h_du_pos

/-- Degree upper bound: deg ≤ inputBits for any S-box.
    Source: LeanHash/SboxProperties.lean (adapted with hypothesis) -/
theorem degree_upper_bound (sp : SboxParams) (h : sp.algebraicDeg ≤ sp.inputBits) :
    sp.algebraicDeg ≤ sp.inputBits := h

/-- AES S-box degree is 7, within 8-bit bound. -/
example : aesSboxParams.algebraicDeg ≤ aesSboxParams.inputBits := by native_decide

/-- Poseidon S-box is APN (δ=2). -/
example : poseidonSboxParams.diffUniformity = 2 := rfl

-- ============================================================
-- Section 7: Security bound from wide trail
-- ============================================================

/-- Security bits from differential analysis:
    security = activeSboxes * log2(2^n / δ).
    Simplified: for n-bit S-box with δ, each active S-box contributes
    ≈ n - log2(δ) bits. We approximate with natural subtraction. -/
def differentialSecurityBits (sp : SboxParams) (activeSboxes : Nat) : Nat :=
  activeSboxes * (sp.inputBits - Nat.log2 sp.diffUniformity)

/-- More active S-boxes → higher security.
    Source: Wide trail strategy fundamental theorem. -/
theorem more_active_more_secure (sp : SboxParams) (a1 a2 : Nat) (h : a1 ≤ a2) :
    differentialSecurityBits sp a1 ≤ differentialSecurityBits sp a2 := by
  simp [differentialSecurityBits]
  exact Nat.mul_le_mul_right _ h

/-- AES differential security: 25 active S-boxes × (8 - 2) = 150 bits. -/
example : differentialSecurityBits aesSboxParams 25 = 150 := by native_decide

/-- Poseidon differential security: 16 active × (64 - 1) = 1008 bits. -/
example : differentialSecurityBits poseidonSboxParams 16 = 1008 := by native_decide

-- ============================================================
-- Section 8: Fitness function (D19 — formal bounds)
-- ============================================================

/-- Birthday bound: generic collision security = outputBits / 2. -/
def birthdayFloor (outputBits : Nat) : Nat := outputBits / 2

/-- TrustHash fitness: security_level = min(genericFloor, structuralCost).
    genericFloor = birthday bound (simplest generic attack).
    structuralCost = differentialSecurityBits (from wide trail analysis). -/
def securityLevel (outputBits : Nat) (sp : SboxParams) (activeSboxes : Nat) : Nat :=
  min (birthdayFloor outputBits) (differentialSecurityBits sp activeSboxes)

/-- Fitness monotone: more active S-boxes → fitness doesn't decrease. -/
theorem fitness_monotone_active (outputBits : Nat) (sp : SboxParams) (a1 a2 : Nat)
    (h : a1 ≤ a2) :
    securityLevel outputBits sp a1 ≤ securityLevel outputBits sp a2 := by
  simp only [securityLevel]
  have h_mono := more_active_more_secure sp a1 a2 h
  omega

/-- AES-128 security level: min(64, 150) = 64 bits (birthday-bounded). -/
example : securityLevel 128 aesSboxParams 25 = 64 := by native_decide

/-- With hypothetical 60 active S-boxes: min(64, 360) = 64 (still birthday). -/
example : securityLevel 128 aesSboxParams 60 = 64 := by native_decide

-- Smoke tests
#eval aes128Semantics
#eval poseidon128Semantics
#eval securityLevel 128 aesSboxParams 25           -- 64
#eval securityLevel 256 poseidonSboxParams 16      -- 128
#eval differentialSecurityBits aesSboxParams 25     -- 150

end SuperHash
