import SuperHash.Rules.SoundRule
import SuperHash.EGraph.Tests
import SuperHash.Pipeline.EMatchSpec

/-!
# SuperHash.Rules.CryptoRules — Concrete rewrite rules for crypto design

Five equivalence rewrite rules for exploring the hash design space.
Each rule carries its soundness proof (LHS = RHS semantically).

Improvement strategies (sboxSubstitute, widenTrail, increaseRounds)
are modeled as node-addition operations that add alternative designs
to the E-graph without merging, preserving ConsistentValuation trivially.
-/

namespace SuperHash

-- ============================================================
-- CryptoExpr: Expression type for semantic reasoning
-- ============================================================

/-- Expression tree mirroring CryptoOp for semantic evaluation.
    v2.0 adds hierarchical block constructors that mirror CryptoOp blocks. -/
inductive CryptoExpr where
  -- v1.0 primitives
  | sbox (degree : Nat) (child : CryptoExpr)
  | linear (branchNum : Nat) (child : CryptoExpr)
  | xor (left right : CryptoExpr)
  | round (degree : Nat) (bn : Nat) (child : CryptoExpr)
  | compose (first second : CryptoExpr)
  | parallel (left right : CryptoExpr)
  | iterate (n : Nat) (body : CryptoExpr)
  | const (val : Nat)
  | var (id : Nat)
  -- v2.0 hierarchical blocks
  | spnBlock (rounds : Nat) (sboxChild linearChild : CryptoExpr)
  | feistelBlock (rounds : Nat) (fChild : CryptoExpr)
  | spongeBlock (rate capacity : Nat) (permChild : CryptoExpr)
  | arxBlock (rounds : Nat) (addChild rotChild xorChild : CryptoExpr)

/-- Evaluate a CryptoExpr given an environment. -/
def CryptoExpr.eval (e : CryptoExpr) (env : Nat → Nat) : Nat :=
  match e with
  | .sbox d c => d * c.eval env
  | .linear b c => b + c.eval env
  | .xor l r => l.eval env + r.eval env
  | .round d b c => d * c.eval env + b
  | .compose f s => f.eval env + s.eval env
  | .parallel l r => l.eval env + r.eval env
  | .iterate n b => n * b.eval env
  | .const v => v
  | .var id => env id
  | .spnBlock r s l => r * (s.eval env + l.eval env)
  | .feistelBlock r f => r * f.eval env
  | .spongeBlock rt cap p => rt * p.eval env + cap
  | .arxBlock r a rot x => r * (a.eval env + rot.eval env + x.eval env)

/-- Evaluator for the SoundRewriteRule interface. -/
def cryptoEval : CryptoExpr → (Nat → Nat) → Nat := CryptoExpr.eval

-- ============================================================
-- Equivalence Rules (5 rules, each with soundness proof)
-- ============================================================

/-- Rule 1: round(d, b, x) ≡ compose(sbox(d, x), const(b))
    A round decomposes into sbox (nonlinear) + constant (linear contribution). -/
def roundComposeRule : EquivalenceRule CryptoOp CryptoExpr Nat where
  name := "roundCompose"
  rule := {
    name := "roundCompose"
    lhs := .node (.round 0 0 0) [.patVar 0]
    rhs := .node (.compose 0 0) [.node (.sbox 0 0) [.patVar 0], .node (.const 0) []]
  }
  lhsExpr := fun vars => .round ((vars 0).eval (fun _ => 0)) ((vars 1).eval (fun _ => 0)) (vars 2)
  rhsExpr := fun vars => .compose (.sbox ((vars 0).eval (fun _ => 0)) (vars 2))
                                   (.const ((vars 1).eval (fun _ => 0)))
  eval := cryptoEval
  soundness := by
    intro env vars
    simp [cryptoEval, CryptoExpr.eval]

/-- Rule 2: iterate(1, x) ≡ x
    Iterating once is the identity. -/
def iterateOneRule : EquivalenceRule CryptoOp CryptoExpr Nat where
  name := "iterateOne"
  rule := {
    name := "iterateOne"
    lhs := .node (.iterate 1 0) [.patVar 0]
    rhs := .patVar 0
  }
  lhsExpr := fun vars => .iterate 1 (vars 0)
  rhsExpr := fun vars => vars 0
  eval := cryptoEval
  soundness := by
    intro env vars
    simp [cryptoEval, CryptoExpr.eval]

/-- Rule 3: compose(compose(a, b), c) ≡ compose(a, compose(b, c))
    Composition is associative. -/
def composeAssocRule : EquivalenceRule CryptoOp CryptoExpr Nat where
  name := "composeAssoc"
  rule := {
    name := "composeAssoc"
    lhs := .node (.compose 0 0) [.node (.compose 0 0) [.patVar 0, .patVar 1], .patVar 2]
    rhs := .node (.compose 0 0) [.patVar 0, .node (.compose 0 0) [.patVar 1, .patVar 2]]
  }
  lhsExpr := fun vars => .compose (.compose (vars 0) (vars 1)) (vars 2)
  rhsExpr := fun vars => .compose (vars 0) (.compose (vars 1) (vars 2))
  eval := cryptoEval
  soundness := by
    intro env vars
    simp [cryptoEval, CryptoExpr.eval]
    omega

/-- Rule 4: parallel(x, const(0)) ≡ x
    Parallel with zero is identity. -/
def parallelIdentityRule : EquivalenceRule CryptoOp CryptoExpr Nat where
  name := "parallelIdentity"
  rule := {
    name := "parallelIdentity"
    lhs := .node (.parallel 0 0) [.patVar 0, .node (.const 0) []]
    rhs := .patVar 0
  }
  lhsExpr := fun vars => .parallel (vars 0) (.const 0)
  rhsExpr := fun vars => vars 0
  eval := cryptoEval
  soundness := by
    intro env vars
    simp [cryptoEval, CryptoExpr.eval]

/-- Rule 5: iterate(m, iterate(n, x)) ≡ iterate(m*n, x)
    Nested iteration composes multiplicatively. -/
def iterateComposeRule : EquivalenceRule CryptoOp CryptoExpr Nat where
  name := "iterateCompose"
  rule := {
    name := "iterateCompose"
    lhs := .node (.iterate 0 0) [.node (.iterate 0 0) [.patVar 0]]
    rhs := .node (.iterate 0 0) [.patVar 0]
  }
  lhsExpr := fun vars => .iterate ((vars 0).eval (fun _ => 0))
                                   (.iterate ((vars 1).eval (fun _ => 0)) (vars 2))
  rhsExpr := fun vars => .iterate (((vars 0).eval (fun _ => 0)) * ((vars 1).eval (fun _ => 0)))
                                   (vars 2)
  eval := cryptoEval
  soundness := by
    intro env vars
    simp [cryptoEval, CryptoExpr.eval]
    exact (Nat.mul_assoc _ _ _).symm

-- ============================================================
-- Improvement Strategies (node-addition, not merging)
-- ============================================================

/-- An improvement strategy adds an alternative design node to the E-graph.
    Does NOT merge (preserves CV trivially via add_node_consistent). -/
structure ImprovementStrategy where
  name : String
  /-- Given an existing node, produce an improved alternative (if applicable). -/
  improve : CryptoOp → Option CryptoOp
  /-- The improved design has ≥ local cost (indicating ≥ security). -/
  cost_improves : ∀ op op', improve op = some op' →
    CryptoOp.localCost op' ≥ CryptoOp.localCost op

/-- Strategy: substitute S-box with higher degree. -/
def sboxSubstituteStrategy : ImprovementStrategy where
  name := "sboxSubstitute"
  improve := fun
    | .sbox d c => if d < 11 then some (.sbox 11 c) else none
    | _ => none
  cost_improves := by
    intro op op' h
    cases op <;> simp at h
    · rename_i d c; obtain ⟨_, rfl⟩ := h; simp [CryptoOp.localCost]; omega

/-- Strategy: widen MDS branch number. -/
def widenTrailStrategy : ImprovementStrategy where
  name := "widenTrail"
  improve := fun
    | .linear b c => if b < 5 then some (.linear 5 c) else none
    | _ => none
  cost_improves := by
    intro op op' h
    cases op <;> simp at h
    · rename_i b c; obtain ⟨_, rfl⟩ := h; simp [CryptoOp.localCost]; omega

/-- Strategy: increase iteration count. -/
def increaseRoundsStrategy : ImprovementStrategy where
  name := "increaseRounds"
  improve := fun
    | .iterate n b => some (.iterate (n + 2) b)
    | _ => none
  cost_improves := by
    intro op op' h
    cases op <;> simp at h
    · rename_i n b; obtain rfl := h; simp [CryptoOp.localCost]

-- Non-vacuity: strategy cost_improves is satisfiable
example : CryptoOp.localCost (.sbox 11 0) ≥ CryptoOp.localCost (.sbox 5 0) :=
  sboxSubstituteStrategy.cost_improves _ _ rfl

example : CryptoOp.localCost (.linear 5 0) ≥ CryptoOp.localCost (.linear 3 0) :=
  widenTrailStrategy.cost_improves _ _ rfl

example : CryptoOp.localCost (.iterate 10 0) ≥ CryptoOp.localCost (.iterate 8 0) :=
  increaseRoundsStrategy.cost_improves _ _ rfl

-- Smoke tests
#eval roundComposeRule.name        -- "roundCompose"
#eval iterateOneRule.name          -- "iterateOne"
#eval sboxSubstituteStrategy.improve (.sbox 5 0)    -- some (sbox 11 0)
#eval widenTrailStrategy.improve (.linear 3 0)       -- some (linear 5 0)
#eval increaseRoundsStrategy.improve (.iterate 8 0)  -- some (iterate 10 0)

-- ============================================================
-- PatternSoundRule instances (bridge to pipeline)
-- ============================================================

/-! The pipeline takes `PatternSoundRule CryptoOp Nat` which proves soundness
    at the `Pattern.eval` / `NodeSemantics.evalOp` level. These instances
    use corrected skeleton child IDs (e.g., `.compose 0 1` not `.compose 0 0`)
    to satisfy `AllDistinctChildren`. -/

set_option linter.unusedSimpArgs false

-- Helper lemmas for reducing `decide` on concrete Nat equalities in Pattern.eval proofs
private theorem decide_reduce_True : decide True = true := rfl
private theorem decide_reduce_False : decide False = false := rfl
private theorem decide_reduce_01 : decide (0 = 1) = false := rfl
private theorem decide_reduce_10 : decide (1 = 0) = false := rfl

/-- PatternSoundRule: iterate(1, x) = x (identity). Soundness: 1 * σ 0 = σ 0. -/
def iterateOne_psound : PatternSoundRule CryptoOp Nat where
  rule := { name := "iterateOne", lhs := .node (.iterate 1 0) [.patVar 0], rhs := .patVar 0 }
  soundness := by
    intro env σ
    simp only [Pattern.eval, NodeOps.children, CryptoOp.children, NodeSemantics.evalOp,
      evalCryptoOpSem, List.map, List.zip, List.zipWith, List.lookup,
      BEq.beq, Nat.beq, Inhabited.default, instInhabitedNat,
      decide_reduce_True, decide_reduce_False]; omega
  lhs_wf := by simp [AllDistinctChildren, NodeOps.children, CryptoOp.children, List.Nodup]
  rhs_wf := by simp [AllDistinctChildren]

/-- PatternSoundRule: parallel(x, const(0)) = x (identity). Soundness: σ 0 + 0 = σ 0. -/
def parallelIdentity_psound : PatternSoundRule CryptoOp Nat where
  rule := { name := "parallelIdentity",
            lhs := .node (.parallel 0 1) [.patVar 0, .node (.const 0) []],
            rhs := .patVar 0 }
  soundness := by
    intro env σ
    simp only [Pattern.eval, NodeOps.children, CryptoOp.children, NodeSemantics.evalOp,
      evalCryptoOpSem, List.map, List.zip, List.zipWith, List.lookup,
      BEq.beq, Nat.beq, Inhabited.default, instInhabitedNat,
      decide_reduce_True, decide_reduce_False, decide_reduce_01, decide_reduce_10]; omega
  lhs_wf := by simp [AllDistinctChildren, NodeOps.children, CryptoOp.children, List.Nodup]
  rhs_wf := by simp [AllDistinctChildren]

/-- PatternSoundRule: compose(compose(x,y),z) = compose(x,compose(y,z)) (assoc).
    Soundness: (σ 0 + σ 1) + σ 2 = σ 0 + (σ 1 + σ 2). -/
def composeAssoc_psound : PatternSoundRule CryptoOp Nat where
  rule := { name := "composeAssoc",
            lhs := .node (.compose 0 1) [.node (.compose 0 1) [.patVar 0, .patVar 1], .patVar 2],
            rhs := .node (.compose 0 1) [.patVar 0, .node (.compose 0 1) [.patVar 1, .patVar 2]] }
  soundness := by
    intro env σ
    simp only [Pattern.eval, NodeOps.children, CryptoOp.children, NodeSemantics.evalOp,
      evalCryptoOpSem, List.map, List.zip, List.zipWith, List.lookup,
      BEq.beq, Nat.beq, Inhabited.default, instInhabitedNat]
    simp only [decide_reduce_True, decide_reduce_False, decide_reduce_01, decide_reduce_10]; omega
  lhs_wf := by simp [AllDistinctChildren, NodeOps.children, CryptoOp.children, List.Nodup]
  rhs_wf := by simp [AllDistinctChildren, NodeOps.children, CryptoOp.children, List.Nodup]

/-- PatternSoundRule: round(d,b,x) = compose(sbox(d,x), const(b)).
    Soundness: d * σ 0 + b = (d * σ 0) + b. -/
def roundCompose_psound (d b : Nat) : PatternSoundRule CryptoOp Nat where
  rule := { name := "roundCompose",
            lhs := .node (.round d b 0) [.patVar 0],
            rhs := .node (.compose 0 1) [.node (.sbox d 0) [.patVar 0], .node (.const b) []] }
  soundness := by
    intro env σ
    simp only [Pattern.eval, NodeOps.children, CryptoOp.children, NodeSemantics.evalOp,
      evalCryptoOpSem, List.map, List.zip, List.zipWith, List.lookup,
      BEq.beq, Nat.beq, Inhabited.default, instInhabitedNat]
    simp only [decide_reduce_True, decide_reduce_False, decide_reduce_01, decide_reduce_10]
  lhs_wf := by simp [AllDistinctChildren, NodeOps.children, CryptoOp.children, List.Nodup]
  rhs_wf := by simp [AllDistinctChildren, NodeOps.children, CryptoOp.children, List.Nodup]

/-- PatternSoundRule: iterate(n, iterate(m, x)) = iterate(n*m, x).
    Soundness: n * (m * σ 0) = (n * m) * σ 0. -/
def iterateCompose_psound (n m : Nat) : PatternSoundRule CryptoOp Nat where
  rule := { name := "iterateCompose",
            lhs := .node (.iterate n 0) [.node (.iterate m 0) [.patVar 0]],
            rhs := .node (.iterate (n * m) 0) [.patVar 0] }
  soundness := by
    intro env σ
    simp only [Pattern.eval, NodeOps.children, CryptoOp.children, NodeSemantics.evalOp,
      evalCryptoOpSem, List.map, List.zip, List.zipWith, List.lookup,
      BEq.beq, Inhabited.default, instInhabitedNat,
      decide_reduce_True]
    exact (Nat.mul_assoc n m (σ 0)).symm
  lhs_wf := by simp [AllDistinctChildren, NodeOps.children, CryptoOp.children, List.Nodup]
  rhs_wf := by simp [AllDistinctChildren, NodeOps.children, CryptoOp.children, List.Nodup]

/-- Convenience: all 5 PatternSoundRules for use with the pipeline. -/
def cryptoPatternRules : List (PatternSoundRule CryptoOp Nat) :=
  [iterateOne_psound, parallelIdentity_psound, composeAssoc_psound,
   roundCompose_psound 7 5, iterateCompose_psound 10 2]

-- Smoke tests
#check iterateOne_psound
#check parallelIdentity_psound
#check composeAssoc_psound
#check @roundCompose_psound
#check @iterateCompose_psound
#eval cryptoPatternRules.length  -- 5

end SuperHash
