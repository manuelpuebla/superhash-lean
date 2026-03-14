/-
  SuperHash — Extractable Typeclass + Generic Extraction
  Fase 3 Subfase 1: Domain-agnostic expression extraction from e-graphs.

  Key components:
  - `Extractable` typeclass: reconstruct expressions from e-graph nodes
  - `EvalExpr` typeclass: evaluate extracted expressions
  - `ExtractableSound`: soundness law connecting reconstruction to node semantics
  - `extractF` : fuel-based extraction following bestNode pointers
  - `mapOption` : total helper for extracting all children (with spec lemmas for F3S2)
-/
import SuperHash.EGraph.Consistency

namespace SuperHash

open UnionFind

-- ══════════════════════════════════════════════════════════════════
-- Helper: mapOption (total, with spec lemmas for F3S2 proofs)
-- ══════════════════════════════════════════════════════════════════

/-- Apply `f` to each element, collecting results.
    Returns `none` if any application returns `none`. -/
def mapOption (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | a :: as =>
    match f a with
    | none => none
    | some b =>
      match mapOption f as with
      | none => none
      | some bs => some (b :: bs)

@[simp] theorem mapOption_nil (f : α → Option β) : mapOption f [] = some [] := rfl

/-- Inversion lemma for cons case. -/
theorem mapOption_cons_inv {f : α → Option β} {a : α} {as : List α} {results : List β}
    (h : mapOption f (a :: as) = some results) :
    ∃ b bs, f a = some b ∧ mapOption f as = some bs ∧ results = b :: bs := by
  simp only [mapOption] at h
  split at h
  · exact absurd h (by simp)
  · rename_i b hb
    split at h
    · exact absurd h (by simp)
    · rename_i bs hbs
      exact ⟨b, bs, hb, hbs, (Option.some.inj h).symm⟩

theorem mapOption_cons_some {f : α → Option β} {a : α} {as : List α}
    {b : β} {bs : List β}
    (hf : f a = some b) (hrest : mapOption f as = some bs) :
    mapOption f (a :: as) = some (b :: bs) := by
  simp [mapOption, hf, hrest]

theorem mapOption_length {f : α → Option β} {l : List α} {results : List β}
    (h : mapOption f l = some results) : results.length = l.length := by
  induction l generalizing results with
  | nil => simp [mapOption] at h; subst h; rfl
  | cons a as ih =>
    obtain ⟨b, bs, _, hrest, hrsl⟩ := mapOption_cons_inv h
    subst hrsl
    simp [ih hrest]

theorem mapOption_get {f : α → Option β} {l : List α} {results : List β}
    (h : mapOption f l = some results)
    (i : Nat) (hil : i < l.length) (hir : i < results.length) :
    f l[i] = some results[i] := by
  induction l generalizing results i with
  | nil => exact absurd hil (Nat.not_lt_zero _)
  | cons a as ih =>
    obtain ⟨b, bs, hfa, hrest, hrsl⟩ := mapOption_cons_inv h
    subst hrsl
    match i with
    | 0 => exact hfa
    | i + 1 =>
      exact ih hrest i (Nat.lt_of_succ_lt_succ hil) (Nat.lt_of_succ_lt_succ hir)

-- ══════════════════════════════════════════════════════════════════
-- Extractable + EvalExpr Typeclasses
-- ══════════════════════════════════════════════════════════════════

/-- Typeclass for reconstructing expressions from e-graph nodes.
    Any domain (circuits, lambda calculus, arithmetic) can instantiate this. -/
class Extractable (Op : Type) (Expr : Type) where
  /-- Reconstruct an expression from an op and its children's extracted expressions. -/
  reconstruct : Op → List Expr → Option Expr

/-- Typeclass for evaluating extracted expressions.
    `Val` is the semantic domain (e.g., ZMod p for circuits, Nat for arithmetic). -/
class EvalExpr (Expr : Type) (Val : Type) where
  /-- Evaluate an expression given an environment for external inputs. -/
  evalExpr : Expr → (Nat → Val) → Val

/-- Soundness law connecting Extractable + EvalExpr to NodeSemantics.
    If reconstruction succeeds and each child expression evaluates to the
    value of its corresponding child class, then the reconstructed expression
    evaluates to `NodeSemantics.evalOp` applied to those child values.

    This is the key bridge: extracted `Expr` semantics ↔ e-graph `NodeSemantics`. -/
def ExtractableSound (Op Expr Val : Type) [NodeOps Op] [NodeSemantics Op Val]
    [Extractable Op Expr] [EvalExpr Expr Val] : Prop :=
  ∀ (op : Op) (childExprs : List Expr) (expr : Expr)
    (env : Nat → Val) (v : EClassId → Val),
  Extractable.reconstruct op childExprs = some expr →
  childExprs.length = (NodeOps.children op).length →
  (∀ (i : Nat) (hi : i < childExprs.length) (hio : i < (NodeOps.children op).length),
    EvalExpr.evalExpr childExprs[i] env =
      v ((NodeOps.children op)[i]'hio)) →
  EvalExpr.evalExpr expr env = NodeSemantics.evalOp op env v

-- ══════════════════════════════════════════════════════════════════
-- Generic extractF: fuel-based extraction via bestNode
-- ══════════════════════════════════════════════════════════════════

variable {Op : Type} {Expr : Type}
  [NodeOps Op] [BEq Op] [Hashable Op]
  [Extractable Op Expr]

/-- Extract an expression from the e-graph starting at class `id`.
    Follows `bestNode` pointers set by `computeCosts`.
    Uses fuel for termination (fuel ≥ numClasses suffices for acyclic graphs).

    Returns `some expr` if extraction succeeds, `none` if fuel runs out,
    class not found, or no bestNode is set. -/
def extractF (g : EGraph Op) (id : EClassId) : Nat → Option Expr
  | 0 => none
  | fuel + 1 =>
    let canonId := root g.unionFind id
    match g.classes.get? canonId with
    | none => none
    | some eclass =>
      match eclass.bestNode with
      | none => none
      | some bestNode =>
        let children := NodeOps.children bestNode.op
        match mapOption (fun c => extractF g c fuel) children with
        | none => none
        | some childExprs => Extractable.reconstruct bestNode.op childExprs

-- ══════════════════════════════════════════════════════════════════
-- Basic lemmas
-- ══════════════════════════════════════════════════════════════════

/-- extractF with zero fuel always returns none. -/
@[simp] theorem extractF_zero (g : EGraph Op) (id : EClassId) :
    extractF g id 0 = (none : Option Expr) := rfl

/-- Convenience: extract with fuel = numClasses + 1. -/
def extractAuto (g : EGraph Op) (rootId : EClassId) : Option Expr :=
  extractF g rootId (g.numClasses + 1)


/-
  SuperHash — Extraction Correctness Specification
  Fase 3 Subfase 2: Formal verification of greedy extraction

  Key theorem:
  - `extractF_correct`: if ConsistentValuation + BestNodeInv + ExtractableSound,
    then extractF returns an expression that evaluates to the correct value.

  Proof strategy:
  - Induction on fuel
  - BestNodeInv provides: bestNode ∈ class.nodes
  - ConsistentValuation node-consistency provides: NodeEval bestNode v = v classId
  - ExtractableSound bridges: evalExpr expr = evalOp op
  - Fuel descent ensures well-founded recursion
-/


open UnionFind

variable {Op : Type} {Val : Type} {Expr : Type}
  [NodeOps Op] [BEq Op] [Hashable Op]
  [LawfulBEq Op] [LawfulHashable Op]
  [NodeSemantics Op Val]
  [Extractable Op Expr] [EvalExpr Expr Val]

-- ══════════════════════════════════════════════════════════════════
-- extractF_correct: Greedy extraction produces correct expressions
-- ══════════════════════════════════════════════════════════════════

/-- Greedy extraction produces semantically correct expressions.

    If:
    - `ConsistentValuation g env v` (e-graph semantics are consistent)
    - `BestNodeInv g.classes` (every bestNode is in its class's nodes)
    - `ExtractableSound Op Expr Val` (reconstruction preserves semantics)
    - `extractF g classId fuel = some expr`

    Then: `EvalExpr.evalExpr expr env = v (root g.unionFind classId)`

    Proof: induction on fuel.
    - Base (fuel = 0): extractF returns none — vacuously true.
    - Step (fuel + 1):
      1. bestNode ∈ class.nodes (from BestNodeInv)
      2. NodeEval bestNode env v = v classId (from ConsistentValuation)
      3. Each child extraction returns correct value (by IH on fuel)
      4. Extractable.reconstruct produces expr with correct eval (by ExtractableSound)
-/
theorem extractF_correct (g : EGraph Op) (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (hsound : ExtractableSound Op Expr Val) :
    ∀ (fuel : Nat) (classId : EClassId) (expr : Expr),
      extractF g classId fuel = some expr →
      EvalExpr.evalExpr expr env = v (root g.unionFind classId) := by
  intro fuel
  induction fuel with
  | zero => intro classId expr h; simp [extractF] at h
  | succ n ih =>
    intro classId expr hext
    unfold extractF at hext
    simp only [] at hext
    split at hext
    · exact absurd hext (by simp)
    · rename_i eclass heclass
      split at hext
      · exact absurd hext (by simp)
      · rename_i bestNode hbestNode
        split at hext
        · exact absurd hext (by simp)
        · rename_i childExprs hmapOpt
          -- bestNode ∈ eclass.nodes (from BestNodeInv)
          have hbn_mem := hbni _ _ _ heclass hbestNode
          -- NodeEval bestNode evaluates to v (root classId) (from ConsistentValuation)
          have heval := hcv.2 (root g.unionFind classId) eclass heclass bestNode hbn_mem
          -- children lengths match
          have hlen := mapOption_length hmapOpt
          -- each child expression evaluates correctly (by IH)
          have hchildren : ∀ (i : Nat) (hi : i < childExprs.length)
              (hio : i < (NodeOps.children bestNode.op).length),
              EvalExpr.evalExpr childExprs[i] env =
                v ((NodeOps.children bestNode.op)[i]'hio) := by
            intro i hi hio
            have hget := mapOption_get hmapOpt i hio hi
            simp only [] at hget
            rw [ih _ _ hget]
            exact consistent_root_eq' g env v hcv hwf _
          -- bridge: evalExpr expr = evalOp bestNode.op (from ExtractableSound)
          rw [hsound bestNode.op childExprs expr env v hext hlen hchildren]
          -- goal: NodeSemantics.evalOp bestNode.op env v = v (root classId)
          exact heval

/-- Corollary: extractAuto is also correct. -/
theorem extractAuto_correct (g : EGraph Op) (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (hsound : ExtractableSound Op Expr Val)
    (rootId : EClassId) (expr : Expr)
    (hext : extractAuto g rootId = some expr) :
    EvalExpr.evalExpr expr env = v (root g.unionFind rootId) :=
  extractF_correct g env v hcv hwf hbni hsound _ rootId expr hext

-- ══════════════════════════════════════════════════════════════════
-- computeCostsF preserves BestNodeInv + ConsistentValuation
-- (already proven in SemanticSpec.lean, re-exported here for convenience)
-- ══════════════════════════════════════════════════════════════════

/-- After computeCostsF, extraction is correct (combines cost computation
    preserving invariants with extraction correctness). -/
theorem computeCostsF_extractF_correct (g : EGraph Op) (costFn : ENode Op → Nat)
    (fuel : Nat) (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (hsound : ExtractableSound Op Expr Val)
    (extractFuel : Nat) (rootId : EClassId) (expr : Expr)
    (hext : extractF (computeCostsF g costFn fuel) rootId extractFuel = some expr) :
    EvalExpr.evalExpr expr env = v (root g.unionFind rootId) := by
  have hcv' := computeCostsF_preserves_consistency g costFn fuel env v hcv
  have hbni' := computeCostsF_bestNode_in_nodes g costFn fuel hbni
  have hwf' : WellFormed (computeCostsF g costFn fuel).unionFind := by
    rw [computeCostsF_preserves_uf]; exact hwf
  have hroot : root (computeCostsF g costFn fuel).unionFind rootId = root g.unionFind rootId := by
    simp [computeCostsF_preserves_uf]
  rw [hroot] at *
  exact extractF_correct (computeCostsF g costFn fuel) env v hcv' hwf' hbni' hsound
    extractFuel rootId expr hext

end SuperHash
