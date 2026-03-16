import SuperHash.Crypto.CryptoEval
import SuperHash.EGraph.Consistency

/-!
# SuperHash.Crypto.CryptoNodeSemantics — NodeSemantics CryptoOp CryptoSemantics

v2.7 T3: Creates the `NodeSemantics CryptoOp CryptoSemantics` instance so that
the entire verified E-graph pipeline (saturation, extraction, soundness) operates
over real cryptographic metrics instead of Nat arithmetic.

## Architecture
The pipeline infrastructure is parametric over `[NodeSemantics Op Val]`:
- `saturateF_preserves_consistent_internal` — polymorphic
- `optimizeF_soundness` — polymorphic
- `sameShapeSemantics_holds` — auto-proved for ANY Val

This file provides the missing instance, which makes all pipeline theorems
automatically available for `Val := CryptoSemantics`.

## Evaluator semantics (same as CryptoEval.lean but in NodeSemantics format)
- Children accessed via `v : EClassId → CryptoSemantics` (not List)
- Each CryptoOp constructor computes real crypto metrics
- compose: degree multiplies (sequential), xor: degree = max (parallel)
-/

set_option linter.unusedSimpArgs false

namespace SuperHash

-- ============================================================
-- Section 1: CryptoSemantics evaluator for NodeSemantics interface
-- ============================================================

/-- Evaluate CryptoOp in CryptoSemantics domain via NodeSemantics interface.
    Children are accessed via `v : EClassId → CryptoSemantics`.
    Same semantics as evalCryptoSem (CryptoEval.lean) but different interface. -/
def evalCryptoOpCS (op : CryptoOp) (_env : Nat → CryptoSemantics)
    (v : EClassId → CryptoSemantics) : CryptoSemantics :=
  match op with
  | .sbox d c =>
    let child := v c
    { algebraicDegree := d * child.algebraicDegree
      differentialUniformity := child.differentialUniformity
      linearBias := child.linearBias
      branchNumber := child.branchNumber
      activeMinSboxes := child.activeMinSboxes + 1
      latency := child.latency + 1
      gateCount := child.gateCount + d
      circuitDepth := child.circuitDepth + 1 }
  | .linear bn c =>
    let child := v c
    { algebraicDegree := child.algebraicDegree
      differentialUniformity := child.differentialUniformity
      linearBias := child.linearBias
      branchNumber := bn
      activeMinSboxes := child.activeMinSboxes
      latency := child.latency + 1
      gateCount := child.gateCount + bn
      circuitDepth := child.circuitDepth + 1 }
  | .xor l r =>
    let vl := v l; let vr := v r
    { algebraicDegree := max vl.algebraicDegree vr.algebraicDegree
      differentialUniformity := max vl.differentialUniformity vr.differentialUniformity
      linearBias := max vl.linearBias vr.linearBias
      branchNumber := min vl.branchNumber vr.branchNumber
      activeMinSboxes := max vl.activeMinSboxes vr.activeMinSboxes
      latency := max vl.latency vr.latency + 1
      gateCount := vl.gateCount + vr.gateCount + 1
      circuitDepth := max vl.circuitDepth vr.circuitDepth + 1 }
  | .round d bn c =>
    let child := v c
    { algebraicDegree := d * child.algebraicDegree
      differentialUniformity := child.differentialUniformity
      linearBias := child.linearBias
      branchNumber := bn
      activeMinSboxes := child.activeMinSboxes + 1
      latency := child.latency + 2
      gateCount := child.gateCount + d + bn
      circuitDepth := child.circuitDepth + 2 }
  | .compose f s =>
    let vf := v f; let vs := v s
    { algebraicDegree := vf.algebraicDegree * vs.algebraicDegree
      differentialUniformity := max vf.differentialUniformity vs.differentialUniformity
      linearBias := max vf.linearBias vs.linearBias
      branchNumber := min vf.branchNumber vs.branchNumber
      activeMinSboxes := vf.activeMinSboxes + vs.activeMinSboxes
      latency := vf.latency + vs.latency
      gateCount := vf.gateCount + vs.gateCount
      circuitDepth := vf.circuitDepth + vs.circuitDepth }
  | .parallel l r =>
    let vl := v l; let vr := v r
    { algebraicDegree := max vl.algebraicDegree vr.algebraicDegree
      differentialUniformity := max vl.differentialUniformity vr.differentialUniformity
      linearBias := max vl.linearBias vr.linearBias
      branchNumber := min vl.branchNumber vr.branchNumber
      activeMinSboxes := vl.activeMinSboxes + vr.activeMinSboxes
      latency := max vl.latency vr.latency
      gateCount := vl.gateCount + vr.gateCount
      circuitDepth := max vl.circuitDepth vr.circuitDepth }
  | .iterate n b =>
    let body := v b
    { algebraicDegree := safePow body.algebraicDegree n
      differentialUniformity := body.differentialUniformity
      linearBias := body.linearBias
      branchNumber := body.branchNumber
      activeMinSboxes := n * body.activeMinSboxes
      latency := n * body.latency
      gateCount := n * body.gateCount
      circuitDepth := n * body.circuitDepth }
  | .const val =>
    { algebraicDegree := val
      differentialUniformity := 0
      linearBias := 0
      branchNumber := 0
      activeMinSboxes := 0
      latency := 0
      gateCount := 0
      circuitDepth := 0 }
  | .spnBlock r s l =>
    let vs := v s; let vl := v l
    { algebraicDegree := safePow (vs.algebraicDegree * vl.algebraicDegree) r
      differentialUniformity := max vs.differentialUniformity vl.differentialUniformity
      linearBias := max vs.linearBias vl.linearBias
      branchNumber := vl.branchNumber
      activeMinSboxes := r * (mds_branchNumber vl.branchNumber) / 2
      latency := r * (vs.latency + vl.latency)
      gateCount := r * (vs.gateCount + vl.gateCount)
      circuitDepth := r * (vs.circuitDepth + vl.circuitDepth) }
  | .feistelBlock r f =>
    let vf := v f
    { algebraicDegree := safePow vf.algebraicDegree r
      differentialUniformity := vf.differentialUniformity
      linearBias := vf.linearBias
      branchNumber := vf.branchNumber
      activeMinSboxes := r * vf.activeMinSboxes
      latency := r * vf.latency
      gateCount := r * vf.gateCount
      circuitDepth := r * vf.circuitDepth }
  | .spongeBlock rt cap p =>
    let vp := v p
    { algebraicDegree := safePow vp.algebraicDegree rt
      differentialUniformity :=
        if cap > 0 then min vp.differentialUniformity (2 ^ cap)
        else vp.differentialUniformity
      linearBias := vp.linearBias
      branchNumber := vp.branchNumber
      activeMinSboxes := rt * vp.activeMinSboxes
      latency := rt * vp.latency + cap
      gateCount := rt * vp.gateCount
      circuitDepth := rt * vp.circuitDepth }
  | .arxBlock r a rot x =>
    let va := v a; let vrot := v rot; let vx := v x
    { algebraicDegree := safePow (va.algebraicDegree + vrot.algebraicDegree + vx.algebraicDegree) r
      differentialUniformity := max va.differentialUniformity (max vrot.differentialUniformity vx.differentialUniformity)
      linearBias := max va.linearBias (max vrot.linearBias vx.linearBias)
      branchNumber := min va.branchNumber (min vrot.branchNumber vx.branchNumber)
      activeMinSboxes := r * (va.activeMinSboxes + vrot.activeMinSboxes + vx.activeMinSboxes)
      latency := r * (va.latency + vrot.latency + vx.latency)
      gateCount := r * (va.gateCount + vrot.gateCount + vx.gateCount)
      circuitDepth := r * (va.circuitDepth + vrot.circuitDepth + vx.circuitDepth) }

-- ============================================================
-- Section 2: NodeSemantics proof obligations
-- ============================================================

private theorem evalOp_ext_cs (op : CryptoOp) (_env : Nat → CryptoSemantics)
    (v v' : EClassId → CryptoSemantics)
    (h : ∀ c ∈ NodeOps.children op, v c = v' c) :
    evalCryptoOpCS op _env v = evalCryptoOpCS op _env v' := by
  cases op <;> simp only [evalCryptoOpCS, NodeOps.children, CryptoOp.children,
    List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq, false_or] at h ⊢
  all_goals (first
    | (obtain ⟨h1, h2, h3⟩ := h; rw [h1, h2, h3])
    | (obtain ⟨h1, h2⟩ := h; rw [h1, h2])
    | (rw [h])
    | rfl)

private theorem evalOp_mapChildren_cs (f : EClassId → EClassId) (op : CryptoOp)
    (env : Nat → CryptoSemantics) (v : EClassId → CryptoSemantics) :
    evalCryptoOpCS (NodeOps.mapChildren f op) env v =
    evalCryptoOpCS op env (fun c => v (f c)) := by
  cases op <;> simp [evalCryptoOpCS, NodeOps.mapChildren, CryptoOp.mapChildren]

private theorem evalOp_skeleton_cs
    (op₁ op₂ : CryptoOp) (env : Nat → CryptoSemantics)
    (v₁ v₂ : EClassId → CryptoSemantics)
    (hskel : NodeOps.mapChildren (fun _ => (0 : EClassId)) op₁ =
             NodeOps.mapChildren (fun _ => (0 : EClassId)) op₂)
    (hvals : ∀ (i : Nat) (h₁ : i < (NodeOps.children op₁).length)
                (h₂ : i < (NodeOps.children op₂).length),
             v₁ ((NodeOps.children op₁)[i]) = v₂ ((NodeOps.children op₂)[i])) :
    evalCryptoOpCS op₁ env v₁ = evalCryptoOpCS op₂ env v₂ := by
  -- Strategy: use evalOp_ext (which we just proved above) to reduce to children equality,
  -- then use the skeleton + hvals hypotheses.
  -- The skeleton proof follows the same structure as the Nat version,
  -- but we avoid unfolding evalCryptoOpCS into 7-field conjunctions.
  -- Use the Nat version's evalOp_skeleton as a template.
  -- The CryptoSemantics version is IDENTICAL in proof structure:
  -- same constructor matching, same hskel/hvals decomposition.
  -- The only difference is the Val type (CryptoSemantics vs Nat).
  -- Key insight: evalCryptoOpCS produces a CryptoSemantics struct,
  -- and `rw` on struct equality substitutes all 7 field projections at once.
  cases op₁ <;> cases op₂ <;>
    simp [NodeOps.mapChildren, CryptoOp.mapChildren] at hskel <;>
    simp [evalCryptoOpCS, NodeOps.children, CryptoOp.children] at hvals ⊢
  all_goals (first
    | (obtain ⟨rfl, rfl⟩ := hskel; rw [hvals 0 (by omega) (by omega)])
    | (obtain ⟨rfl, rfl⟩ := hskel; rw [hvals])
    | (obtain rfl := hskel
       have h0 := hvals 0 (by omega) (by omega)
       have h1 := hvals 1 (by omega) (by omega)
       have h2 := hvals 2 (by omega) (by omega)
       simp [List.getElem_cons_succ, List.getElem_cons_zero] at h0 h1 h2
       rw [h0, h1, h2])
    | (obtain rfl := hskel
       have h0 := hvals 0 (by omega) (by omega)
       have h1 := hvals 1 (by omega) (by omega)
       simp [List.getElem_cons_succ, List.getElem_cons_zero] at h0 h1
       rw [h0, h1])
    | (obtain rfl := hskel; rw [hvals])
    | (have h0 := hvals 0 (by omega) (by omega)
       have h1 := hvals 1 (by omega) (by omega)
       have h2 := hvals 2 (by omega) (by omega)
       simp [List.getElem_cons_succ, List.getElem_cons_zero] at h0 h1 h2
       rw [h0, h1, h2])
    | (have h0 := hvals 0 (by omega) (by omega)
       have h1 := hvals 1 (by omega) (by omega)
       simp [List.getElem_cons_succ, List.getElem_cons_zero] at h0 h1
       rw [h0, h1])
    | exact hskel
    | rfl)
  -- All remaining goals are reflexivity conjunctions (7 fields all = rfl)
  all_goals simp_all

-- ============================================================
-- Section 3: The instance
-- ============================================================

/-- NodeSemantics instance for CryptoOp over CryptoSemantics domain.
    This is the KEY instance that unlocks the entire verified pipeline
    for real cryptographic metrics. All parametric pipeline theorems
    (saturateF_preserves_consistent, optimizeF_soundness, etc.)
    automatically become available for Val := CryptoSemantics. -/
instance : NodeSemantics CryptoOp CryptoSemantics where
  evalOp := evalCryptoOpCS
  evalOp_ext := evalOp_ext_cs
  evalOp_mapChildren := evalOp_mapChildren_cs
  evalOp_skeleton := evalOp_skeleton_cs

-- ============================================================
-- Section 4: Smoke tests
-- ============================================================

-- Verify the instance works: evaluate sbox(7, child) in CryptoSemantics
#eval evalCryptoOpCS (.sbox 7 0) (fun _ => default) (fun _ => ⟨1, 4, 16, 5, 0, 0, 0, 0⟩)

/-- ConsistentValuation over CryptoSemantics compiles (the type checks). -/
example : ConsistentValuation (Val := CryptoSemantics) (EGraph.empty : EGraph CryptoOp)
    (fun _ => default) (fun _ => default) :=
  empty_consistent _

end SuperHash
