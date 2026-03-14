import SuperHash.Rules.SoundRule
import SuperHash.Rules.CryptoRules

/-!
# SuperHash.Discovery.RuleCandidate — Structure for LLM-proposed rules

v2.0: Defines the `RuleCandidate` type that captures LLM-proposed rewrite rules
before they are verified by the Lean kernel. Includes classification, template
mapping to existing rule types, and serialization for round-trip TCB validation (D11).

## Three-Tier Bridge (D7)
- **Tier 1 (Python)**: LLM generates RuleCandidate JSON
- **Tier 2 (Lean)**: RuleCandidate → verified PatternSoundRule/EquivalenceRule
- **Tier 3**: Bridge theorem proves translation correctness

## Rule Classification (D3)
- `equivalence`: preserves semantics exactly (→ EquivalenceRule)
- `improvement`: improves a metric (→ ImprovementRule / PatternSoundRule)
- `conditional`: applies with side condition (→ ConditionalSoundRewriteRule)
-/

namespace SuperHash

-- CryptoExpr is a recursive inductive; derive Repr for it
deriving instance Repr for CryptoExpr

-- ============================================================
-- Rule classification
-- ============================================================

/-- Classification of a candidate rule. Determines which verified rule type
    the candidate will be translated to after kernel verification. -/
inductive RuleClass where
  | equivalence   -- LHS ≡ RHS semantically (bidirectional)
  | improvement   -- LHS → RHS improves a metric (directional)
  | conditional   -- LHS → RHS with side condition
  deriving Repr, DecidableEq, BEq

instance : ToString RuleClass where
  toString
    | .equivalence => "equivalence"
    | .improvement => "improvement"
    | .conditional => "conditional"

-- ============================================================
-- Rule candidate structure
-- ============================================================

/-- A candidate rewrite rule proposed by an LLM or search algorithm.
    This is the unverified input that goes through the verification pipeline. -/
structure RuleCandidate where
  /-- Human-readable name -/
  name : String
  /-- Classification: equivalence, improvement, or conditional -/
  classification : RuleClass
  /-- LHS pattern as CryptoExpr template -/
  lhsTemplate : CryptoExpr
  /-- RHS pattern as CryptoExpr template -/
  rhsTemplate : CryptoExpr
  /-- Optional side condition description (for conditional rules) -/
  sideCondition : Option String := none
  /-- Source: which LLM/algorithm proposed this -/
  source : String := "unknown"
  /-- Confidence score from the proposer (0.0 to 1.0, encoded as Nat / 100) -/
  confidence : Nat := 50
  deriving Repr

-- ============================================================
-- Verification result
-- ============================================================

/-- Result of attempting to verify a RuleCandidate. -/
inductive VerificationResult where
  | sound       -- Lean kernel accepted the proof
  | unsound     -- Lean kernel rejected or found counterexample
  | timeout     -- Verification exceeded heartbeat/time budget
  | parseError  -- Candidate could not be parsed into valid Lean
  deriving Repr, DecidableEq, BEq

/-- Is the verification result successful? -/
def VerificationResult.isSuccess : VerificationResult → Bool
  | .sound => true
  | _ => false

-- ============================================================
-- Template-based soundness checking
-- ============================================================

/-- Check if a RuleCandidate is semantically sound by evaluating both sides
    on a concrete environment. This is a HEURISTIC pre-check — not a proof.
    Returns true if LHS and RHS agree on the test environment. -/
def RuleCandidate.quickCheck (rc : RuleCandidate) (testEnv : Nat → Nat) : Bool :=
  rc.lhsTemplate.eval testEnv == rc.rhsTemplate.eval testEnv

/-- Check soundness on multiple test environments. -/
def RuleCandidate.multiCheck (rc : RuleCandidate) (envs : List (Nat → Nat)) : Bool :=
  envs.all rc.quickCheck

-- ============================================================
-- Serialization for round-trip TCB validation (D11)
-- ============================================================

/-- Serialize a CryptoExpr to a canonical string form.
    Used for round-trip validation: candidate → source → parse → compare. -/
def CryptoExpr.toCanonical : CryptoExpr → String
  | .sbox d c => s!"(sbox {d} {c.toCanonical})"
  | .linear b c => s!"(linear {b} {c.toCanonical})"
  | .xor l r => s!"(xor {l.toCanonical} {r.toCanonical})"
  | .round d b c => s!"(round {d} {b} {c.toCanonical})"
  | .compose f s => s!"(compose {f.toCanonical} {s.toCanonical})"
  | .parallel l r => s!"(parallel {l.toCanonical} {r.toCanonical})"
  | .iterate n b => s!"(iterate {n} {b.toCanonical})"
  | .const v => s!"(const {v})"
  | .var id => s!"(var {id})"
  | .spnBlock r s l => s!"(spnBlock {r} {s.toCanonical} {l.toCanonical})"
  | .feistelBlock r f => s!"(feistelBlock {r} {f.toCanonical})"
  | .spongeBlock rt cap p => s!"(spongeBlock {rt} {cap} {p.toCanonical})"
  | .arxBlock r a rot x => s!"(arxBlock {r} {a.toCanonical} {rot.toCanonical} {x.toCanonical})"

/-- Serialize a RuleCandidate to canonical string. -/
def RuleCandidate.toCanonical (rc : RuleCandidate) : String :=
  s!"rule:{rc.name}|class:{rc.classification}|lhs:{rc.lhsTemplate.toCanonical}|rhs:{rc.rhsTemplate.toCanonical}"

-- ============================================================
-- Concrete examples
-- ============================================================

/-- Example: SPN block bridge as a RuleCandidate. -/
def exampleSpnBridge : RuleCandidate where
  name := "spnBlockBridge"
  classification := .equivalence
  lhsTemplate := .spnBlock 10 (.var 0) (.var 1)
  rhsTemplate := .iterate 10 (.compose (.var 0) (.var 1))
  source := "manual"
  confidence := 100

/-- Example: round decomposition as a RuleCandidate. -/
def exampleRoundDecomp : RuleCandidate where
  name := "roundDecompose"
  classification := .equivalence
  lhsTemplate := .round 7 5 (.var 0)
  rhsTemplate := .compose (.sbox 7 (.var 0)) (.const 5)
  source := "manual"
  confidence := 100

-- Smoke tests
#eval exampleSpnBridge.quickCheck (fun _ => 3)   -- true
#eval exampleRoundDecomp.quickCheck (fun _ => 3)  -- true
-- toCanonical tests (use #eval! due to Repr sorry in recursive CryptoExpr)
#eval! exampleSpnBridge.toCanonical
#eval! exampleRoundDecomp.toCanonical

/-- Unsound example: changing degree breaks equivalence. -/
def exampleUnsound : RuleCandidate where
  name := "badRule"
  classification := .equivalence
  lhsTemplate := .sbox 7 (.var 0)
  rhsTemplate := .sbox 5 (.var 0)   -- different degree!
  source := "test"

#eval exampleUnsound.quickCheck (fun _ => 3)  -- false (7*3 ≠ 5*3)

end SuperHash
