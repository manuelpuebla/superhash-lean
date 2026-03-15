import SuperHash.Attack.AttackSemantics
import SuperHash.EGraph.Consistency

/-!
# SuperHash.Attack.AttackNodeSemantics — NodeSemantics AttackOp AttackSemantics

Creates the `NodeSemantics AttackOp AttackSemantics` instance so that
the verified E-graph pipeline (saturation, extraction, soundness) operates
over attack metrics. Red Team counterpart to CryptoNodeSemantics.

## Architecture
The pipeline infrastructure is parametric over `[NodeSemantics Op Val]`:
- `saturateF_preserves_consistent_internal` -- polymorphic
- `optimizeF_soundness` -- polymorphic

This file provides the attack-side instance, making all pipeline theorems
automatically available for `Op := AttackOp`, `Val := AttackSemantics`.

## Proof obligations
- `evalOp_ext`: evalOp depends on v only through children
- `evalOp_mapChildren`: mapChildren f commutes with evalOp
- `evalOp_skeleton`: same-skeleton ops evaluate the same with matching children
-/

set_option linter.unusedSimpArgs false

namespace SuperHash

-- ============================================================
-- Section 1: AttackSemantics evaluator for NodeSemantics interface
-- ============================================================

/-- Evaluate AttackOp in AttackSemantics domain via NodeSemantics interface.
    Children are accessed via `v : EClassId → AttackSemantics`.
    Same semantics as evalAttackSem but different interface. -/
def evalAttackOpAS (op : AttackOp) (_env : Nat → AttackSemantics)
    (v : EClassId → AttackSemantics) : AttackSemantics :=
  match op with
  | .diffChar p c =>
    let child := v c
    { timeCost := child.timeCost + 2 * p
      memoryCost := child.memoryCost + p
      dataCost := child.dataCost + p
      successProb := child.successProb + p
      roundsCovered := child.roundsCovered + 1 }
  | .truncatedDiff ab c =>
    let child := v c
    { timeCost := child.timeCost + ab
      memoryCost := child.memoryCost + ab
      dataCost := child.dataCost + ab
      successProb := child.successProb + ab / 2
      roundsCovered := child.roundsCovered + 1 }
  | .boomerang c1 c2 =>
    let v1 := v c1; let v2 := v c2
    { timeCost := v1.timeCost + v2.timeCost + 1
      memoryCost := max v1.memoryCost v2.memoryCost
      dataCost := max v1.dataCost v2.dataCost + 1
      successProb := v1.successProb + v2.successProb
      roundsCovered := v1.roundsCovered + v2.roundsCovered }
  | .impossible r c =>
    let child := v c
    { timeCost := child.timeCost + r
      memoryCost := child.memoryCost + r
      dataCost := child.dataCost
      successProb := child.successProb
      roundsCovered := child.roundsCovered + r }
  | .linearTrail b c =>
    let child := v c
    { timeCost := child.timeCost + 2 * b
      memoryCost := child.memoryCost
      dataCost := child.dataCost + 2 * b
      successProb := child.successProb + b
      roundsCovered := child.roundsCovered + 1 }
  | .linearHull nt c =>
    let child := v c
    { timeCost := child.timeCost + nt
      memoryCost := child.memoryCost + nt
      dataCost := child.dataCost + nt
      successProb := if child.successProb > nt / 2
                     then child.successProb - nt / 2
                     else 0
      roundsCovered := child.roundsCovered + 1 }
  | .algebraicRelation d c =>
    let child := v c
    { timeCost := child.timeCost + d * d
      memoryCost := child.memoryCost + d
      dataCost := child.dataCost
      successProb := child.successProb
      roundsCovered := child.roundsCovered + 1 }
  | .grobnerStep c =>
    let child := v c
    { timeCost := child.timeCost + 3
      memoryCost := child.memoryCost + 3
      dataCost := child.dataCost
      successProb := child.successProb
      roundsCovered := child.roundsCovered }
  | .meetInMiddle sr c1 c2 =>
    let v1 := v c1; let v2 := v c2
    { timeCost := max v1.timeCost v2.timeCost + sr
      memoryCost := v1.memoryCost + v2.memoryCost
      dataCost := max v1.dataCost v2.dataCost
      successProb := v1.successProb + v2.successProb
      roundsCovered := v1.roundsCovered + v2.roundsCovered }
  | .rebound ir or_ c =>
    let child := v c
    { timeCost := child.timeCost + or_
      memoryCost := child.memoryCost + ir
      dataCost := child.dataCost + or_
      successProb := child.successProb + or_
      roundsCovered := child.roundsCovered + ir + or_ }
  | .compose f s =>
    let vf := v f; let vs := v s
    { timeCost := vf.timeCost + vs.timeCost
      memoryCost := max vf.memoryCost vs.memoryCost
      dataCost := max vf.dataCost vs.dataCost
      successProb := vf.successProb + vs.successProb
      roundsCovered := vf.roundsCovered + vs.roundsCovered }
  | .parallel l r =>
    let vl := v l; let vr := v r
    { timeCost := min vl.timeCost vr.timeCost
      memoryCost := min vl.memoryCost vr.memoryCost
      dataCost := min vl.dataCost vr.dataCost
      successProb := min vl.successProb vr.successProb
      roundsCovered := max vl.roundsCovered vr.roundsCovered }
  | .iterate n b =>
    let body := v b
    { timeCost := n * body.timeCost
      memoryCost := body.memoryCost
      dataCost := body.dataCost
      successProb := n * body.successProb
      roundsCovered := n * body.roundsCovered }
  | .const cost =>
    { timeCost := cost
      memoryCost := 0
      dataCost := 0
      successProb := 0
      roundsCovered := 0 }

-- ============================================================
-- Section 2: NodeSemantics proof obligations
-- ============================================================

private theorem evalOp_ext_as (op : AttackOp) (_env : Nat → AttackSemantics)
    (v v' : EClassId → AttackSemantics)
    (h : ∀ c ∈ NodeOps.children op, v c = v' c) :
    evalAttackOpAS op _env v = evalAttackOpAS op _env v' := by
  cases op <;> simp only [evalAttackOpAS, NodeOps.children, AttackOp.children,
    List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq, false_or] at h ⊢
  all_goals (first
    | (obtain ⟨h1, h2⟩ := h; rw [h1, h2])
    | (rw [h])
    | rfl)

private theorem evalOp_mapChildren_as (f : EClassId → EClassId) (op : AttackOp)
    (env : Nat → AttackSemantics) (v : EClassId → AttackSemantics) :
    evalAttackOpAS (NodeOps.mapChildren f op) env v =
    evalAttackOpAS op env (fun c => v (f c)) := by
  cases op <;> simp [evalAttackOpAS, NodeOps.mapChildren, AttackOp.mapChildren]

private theorem evalOp_skeleton_as
    (op₁ op₂ : AttackOp) (env : Nat → AttackSemantics)
    (v₁ v₂ : EClassId → AttackSemantics)
    (hskel : NodeOps.mapChildren (fun _ => (0 : EClassId)) op₁ =
             NodeOps.mapChildren (fun _ => (0 : EClassId)) op₂)
    (hvals : ∀ (i : Nat) (h₁ : i < (NodeOps.children op₁).length)
                (h₂ : i < (NodeOps.children op₂).length),
             v₁ ((NodeOps.children op₁)[i]) = v₂ ((NodeOps.children op₂)[i])) :
    evalAttackOpAS op₁ env v₁ = evalAttackOpAS op₂ env v₂ := by
  cases op₁ <;> cases op₂ <;>
    simp [NodeOps.mapChildren, AttackOp.mapChildren] at hskel <;>
    simp [evalAttackOpAS, NodeOps.children, AttackOp.children] at hvals ⊢
  all_goals (first
    | (obtain ⟨rfl, rfl⟩ := hskel; rw [hvals 0 (by omega) (by omega)])
    | (obtain ⟨rfl, rfl⟩ := hskel; rw [hvals])
    | (obtain rfl := hskel
       have h0 := hvals 0 (by omega) (by omega)
       have h1 := hvals 1 (by omega) (by omega)
       simp [List.getElem_cons_succ, List.getElem_cons_zero] at h0 h1
       rw [h0, h1])
    | (obtain rfl := hskel; rw [hvals])
    | (have h0 := hvals 0 (by omega) (by omega)
       have h1 := hvals 1 (by omega) (by omega)
       simp [List.getElem_cons_succ, List.getElem_cons_zero] at h0 h1
       rw [h0, h1])
    | exact hskel
    | rfl)
  all_goals simp_all

-- ============================================================
-- Section 3: The instance
-- ============================================================

/-- NodeSemantics instance for AttackOp over AttackSemantics domain.
    This is the KEY instance that unlocks the entire verified pipeline
    for attack metrics. All parametric pipeline theorems
    (saturateF_preserves_consistent, optimizeF_soundness, etc.)
    automatically become available for Val := AttackSemantics. -/
instance : NodeSemantics AttackOp AttackSemantics where
  evalOp := evalAttackOpAS
  evalOp_ext := evalOp_ext_as
  evalOp_mapChildren := evalOp_mapChildren_as
  evalOp_skeleton := evalOp_skeleton_as

-- ============================================================
-- Section 4: Smoke tests
-- ============================================================

-- Verify the instance works: evaluate diffChar(6, child) in AttackSemantics
#eval evalAttackOpAS (.diffChar 6 0) (fun _ => default) (fun _ => ⟨0, 0, 0, 0, 0⟩)
-- Expected: {time=12, mem=6, data=6, prob=6, rounds=1}

-- Sequential compose via NodeSemantics interface
#eval evalAttackOpAS (.compose 0 1) (fun _ => default)
  (fun c => if c == 0 then ⟨12, 6, 6, 6, 1⟩ else ⟨28, 0, 28, 14, 1⟩)
-- Expected: {time=40, mem=6, data=28, prob=20, rounds=2}

/-- ConsistentValuation over AttackSemantics compiles (the type checks). -/
example : ConsistentValuation (Val := AttackSemantics) (EGraph.empty : EGraph AttackOp)
    (fun _ => default) (fun _ => default) :=
  empty_consistent _

-- ============================================================
-- Section 5: Non-vacuity examples
-- ============================================================

/-- Non-vacuity: evalOp_ext hypotheses are jointly satisfiable for diffChar. -/
example : evalAttackOpAS (.diffChar 6 0) (fun _ => default) (fun _ => ⟨10, 5, 5, 8, 3⟩) =
    evalAttackOpAS (.diffChar 6 0) (fun _ => default) (fun _ => ⟨10, 5, 5, 8, 3⟩) := rfl

/-- Non-vacuity: evalOp_mapChildren holds for a concrete case. -/
example : evalAttackOpAS (NodeOps.mapChildren (· + 1) (.diffChar 6 0)) (fun _ => default)
    (fun c => if c == 1 then ⟨10, 5, 5, 8, 3⟩ else default) =
    evalAttackOpAS (.diffChar 6 0) (fun _ => default)
    (fun c => if c + 1 == 1 then ⟨10, 5, 5, 8, 3⟩ else default) := by
  simp [evalAttackOpAS, NodeOps.mapChildren, AttackOp.mapChildren]

/-- Non-vacuity: evalOp_skeleton with boomerang (2-child constructor). -/
example : evalAttackOpAS (.boomerang 0 1) (fun _ => default)
    (fun c => if c == 0 then ⟨10, 5, 5, 8, 3⟩ else ⟨14, 8, 6, 8, 3⟩) =
    evalAttackOpAS (.boomerang 2 3) (fun _ => default)
    (fun c => if c == 2 then ⟨10, 5, 5, 8, 3⟩ else ⟨14, 8, 6, 8, 3⟩) := by
  simp [evalAttackOpAS]

end SuperHash
