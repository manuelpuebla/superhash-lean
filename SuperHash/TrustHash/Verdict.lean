import SuperHash.TrustHash.NiceTree
import SuperHash.Crypto.BouraCanteutBound
import SuperHash.Crypto.SourceEntropy
import SuperHash.Crypto.AlgebraicDegree

/-!
# SuperHash.TrustHash.Verdict — Full TrustHash-style security verdict

Computes the complete security verdict using:
1. Generic floor: birthday bound, GBP, Joux
2. Structural cost via DP on tree decomposition
3. BCD11 algebraic degree bounds
4. Wide trail differential bounds

## Formula
```
verdict = min(genericFloor, structuralCost)
structuralCost = min(differentialDP, algebraicDP, bcdAlgebraic)
```

## Source
- TrustHash/Pipeline/PipelineVerdict.lean
- TrustHash/Pipeline/GenericFloorPipeline.lean
- TrustHash/Pipeline/StructuralPipeline.lean
-/

namespace SuperHash.TrustHash

-- ============================================================
-- Section 1: Hash Specification
-- ============================================================

/-- Complete specification of a hash function for security analysis.
    Adapted from TrustHash/HashSpec.lean. -/
structure HashSpec where
  /-- Hash name -/
  name : String
  /-- Output bits -/
  outputBits : Nat
  /-- S-box input bits -/
  sboxBits : Nat
  /-- Number of S-boxes per round -/
  numSboxes : Nat
  /-- S-box algebraic degree -/
  sboxDeg : Nat
  /-- Differential uniformity δ -/
  delta : Nat
  /-- BCD11 propagation constant γ -/
  gamma : Nat
  /-- MDS branch number -/
  branchNumber : Nat
  /-- Number of rounds -/
  numRounds : Nat
  /-- Nice tree decomposition (precomputed) -/
  tree : NiceNode
  deriving Repr

-- ============================================================
-- Section 2: Generic Floor (attack-independent)
-- ============================================================

/-- Birthday bound: collision security ≤ outputBits/2. -/
def birthdayBound (spec : HashSpec) : Nat := spec.outputBits / 2

/-- GBP (Generalized Birthday Problem): for k lists, cost ≈ 2^{n/(1+log2(k))}.
    Simplified: always ≥ birthday bound for standard hash use. -/
def gbpBound (spec : HashSpec) : Nat := spec.outputBits / 2

/-- Generic floor: min of all generic attack bounds. -/
def genericFloor (spec : HashSpec) : Nat :=
  min (birthdayBound spec) (gbpBound spec)

-- ============================================================
-- Section 3: Structural Cost (design-specific)
-- ============================================================

/-- Differential cost via wide trail: activeSboxes × (sboxBits - log2(δ)).
    Source: TrustHash/Pipeline/WideTrailPipeline.lean -/
def differentialCost (spec : HashSpec) : Nat :=
  let activeSboxes := spec.branchNumber * (spec.numRounds / 2)
  sourceEntropy spec.sboxBits activeSboxes spec.delta

/-- Algebraic cost via BCD11 iterated bound + treewidth.
    Source: TrustHash/Pipeline/StructuralPipeline.lean -/
def algebraicCost (spec : HashSpec) : Nat :=
  let totalBits := spec.sboxBits * spec.numSboxes
  let degAfterR := iteratedBcd11 totalBits 0 spec.gamma spec.numRounds
  if degAfterR ≤ 1 then 0
  else spec.tree.treewidth * ilog2 degAfterR

/-- DP-based structural cost: runs security DP on the nice tree.
    Source: TrustHash/DP/SecurityDP.lean -/
def dpCost (spec : HashSpec) : Nat :=
  securityDP spec.tree spec.delta spec.sboxDeg

/-- Higher-order differential cost: 2^{deg+1} queries → deg+1 bits.
    Source: TrustHash via HigherOrderDiff.lean -/
def higherOrderCost (spec : HashSpec) : Nat :=
  let totalBits := spec.sboxBits * spec.numSboxes
  let degAfterR := iteratedBcd11 totalBits 0 spec.gamma spec.numRounds
  degAfterR + 1

/-- Combined structural cost: min of all structural bounds. -/
def structuralCost (spec : HashSpec) : Nat :=
  min (differentialCost spec) (min (algebraicCost spec) (min (dpCost spec) (higherOrderCost spec)))

-- ============================================================
-- Section 4: Full Verdict
-- ============================================================

/-- Complete security verdict. -/
structure Verdict where
  /-- Hash specification -/
  spec : HashSpec
  /-- Generic floor (attack-independent) -/
  generic : Nat
  /-- Differential cost (wide trail) -/
  differential : Nat
  /-- Algebraic cost (BCD11 + treewidth) -/
  algebraic : Nat
  /-- DP cost (tree decomposition DP) -/
  dp : Nat
  /-- Higher-order differential cost -/
  higherOrder : Nat
  /-- Overall security = min(generic, structural) -/
  security : Nat
  /-- Binding constraint -/
  bindingConstraint : String
  /-- Is design optimal? (structural ≥ generic) -/
  isOptimal : Bool
  deriving Repr

/-- Compute the full TrustHash-style verdict for a hash specification. -/
def computeFullVerdict (spec : HashSpec) : Verdict :=
  let gen := genericFloor spec
  let diff := differentialCost spec
  let alg := algebraicCost spec
  let dp := dpCost spec
  let ho := higherOrderCost spec
  let structural := min diff (min alg (min dp ho))
  let overall := min gen structural
  let binding :=
    if overall = gen then "birthday"
    else if overall = diff then "differential"
    else if overall = alg then "algebraic"
    else if overall = dp then "DP"
    else "higher-order"
  { spec := spec
    generic := gen
    differential := diff
    algebraic := alg
    dp := dp
    higherOrder := ho
    security := overall
    bindingConstraint := binding
    isOptimal := structural ≥ gen }

-- ============================================================
-- Section 5: Concrete Hash Specifications
-- ============================================================

/-- AES-128 specification. -/
def aesSpec : HashSpec where
  name := "AES-128"
  outputBits := 128
  sboxBits := 8
  numSboxes := 16
  sboxDeg := 7
  delta := 4
  gamma := 4
  branchNumber := 5
  numRounds := 10
  tree := aesNiceTree

/-- Poseidon-128 (t=3) specification. -/
def poseidonSpec : HashSpec where
  name := "Poseidon-128"
  outputBits := 256
  sboxBits := 64
  numSboxes := 3
  sboxDeg := 5
  delta := 2
  gamma := 4
  branchNumber := 4
  numRounds := 8
  tree := poseidonNiceTree

/-- PRESENT-128 specification. -/
def presentSpec : HashSpec where
  name := "PRESENT-128"
  outputBits := 128
  sboxBits := 4
  numSboxes := 16
  sboxDeg := 3
  delta := 4
  gamma := 4
  branchNumber := 5
  numRounds := 31
  tree := .join (.introduce 0 (.leaf [0])) (.introduce 1 (.leaf [1]))

-- ============================================================
-- Section 6: Compute Verdicts
-- ============================================================

def aesVerdict := computeFullVerdict aesSpec
def poseidonVerdict := computeFullVerdict poseidonSpec
def presentVerdict := computeFullVerdict presentSpec

#eval aesVerdict
#eval poseidonVerdict
#eval presentVerdict

-- ============================================================
-- Section 7: Properties
-- ============================================================

/-- Verdict security ≤ generic floor. -/
theorem verdict_le_generic (spec : HashSpec) :
    (computeFullVerdict spec).security ≤ genericFloor spec :=
  Nat.min_le_left _ _

/-- Verdict security ≤ each structural component. -/
theorem verdict_le_differential (spec : HashSpec) :
    (computeFullVerdict spec).security ≤ differentialCost spec := by
  simp only [computeFullVerdict, Verdict.security]
  omega

/-- More rounds → higher (or equal) differential cost (monotone). -/
theorem differential_mono_rounds (spec1 spec2 : HashSpec)
    (h_same : spec1.branchNumber = spec2.branchNumber ∧
              spec1.sboxBits = spec2.sboxBits ∧
              spec1.delta = spec2.delta)
    (h_rounds : spec1.numRounds ≤ spec2.numRounds) :
    differentialCost spec1 ≤ differentialCost spec2 := by
  simp only [differentialCost]
  obtain ⟨hbn, hn, hd⟩ := h_same
  rw [hbn, hn, hd]
  exact sourceEntropy_mono_active _ _ _ _ (Nat.mul_le_mul_left _ (Nat.div_le_div_right h_rounds))

-- ============================================================
-- Section 8: Non-vacuity
-- ============================================================

/-- AES generic floor = 64 bits. -/
example : (computeFullVerdict aesSpec).generic = 64 := by native_decide

/-- Poseidon generic floor = 128 bits. -/
example : (computeFullVerdict poseidonSpec).generic = 128 := by native_decide

/-- Verdict produces non-trivial security level. -/
example : (computeFullVerdict aesSpec).security > 0 := by native_decide

/-- Poseidon differential cost is very high (not the bottleneck). -/
example : differentialCost poseidonSpec > 128 := by native_decide

end SuperHash.TrustHash
