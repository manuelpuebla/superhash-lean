import SuperHash.Pipeline.Extract
import SuperHash.Rules.CryptoRules
import SuperHash.Crypto.CryptoNodeSemantics

/-!
# SuperHash.Pipeline.Instances — CryptoOp extraction + evaluation instances

Provides:
- `Extractable CryptoOp CryptoExpr`: reconstruct CryptoExpr from e-graph nodes
- `EvalExpr CryptoExpr Nat`: evaluate CryptoExpr in an environment
- `ExtractableSound CryptoOp CryptoExpr Nat`: bridge theorem
- `cryptoCostFn`: cost function for crypto operations
-/

set_option linter.unusedSimpArgs false

namespace SuperHash

-- ============================================================
-- Extractable instance
-- ============================================================

/-- Reconstruct a CryptoExpr from a CryptoOp node and its children's expressions. -/
def reconstructCrypto (op : CryptoOp) (children : List CryptoExpr) : Option CryptoExpr :=
  match op with
  | .sbox d _ => match children with | [c] => some (.sbox d c) | _ => none
  | .linear b _ => match children with | [c] => some (.linear b c) | _ => none
  | .xor _ _ => match children with | [l, r] => some (.xor l r) | _ => none
  | .round d b _ => match children with | [c] => some (.round d b c) | _ => none
  | .compose _ _ => match children with | [f, s] => some (.compose f s) | _ => none
  | .parallel _ _ => match children with | [l, r] => some (.parallel l r) | _ => none
  | .iterate n _ => match children with | [b] => some (.iterate n b) | _ => none
  | .const v => match children with | [] => some (.const v) | _ => none
  | .spnBlock r _ _ => match children with | [s, l] => some (.spnBlock r s l) | _ => none
  | .feistelBlock r _ => match children with | [f] => some (.feistelBlock r f) | _ => none
  | .spongeBlock rt cap _ => match children with | [p] => some (.spongeBlock rt cap p) | _ => none
  | .arxBlock r _ _ _ => match children with | [a, rot, x] => some (.arxBlock r a rot x) | _ => none

instance : Extractable CryptoOp CryptoExpr where
  reconstruct := reconstructCrypto

instance : EvalExpr CryptoExpr Nat where
  evalExpr := CryptoExpr.eval

-- ============================================================
-- ExtractableSound
-- ============================================================

private def childSimpLemmas := [``NodeOps.children, ``CryptoOp.children,
  ``EvalExpr.evalExpr, ``List.getElem_cons_succ, ``List.getElem_cons_zero]

/-- ExtractableSound for CryptoOp/CryptoExpr/Nat. -/
theorem crypto_extractable_sound : ExtractableSound CryptoOp CryptoExpr Nat := by
  intro op childExprs expr env v hrecon hlen hchildren
  simp only [Extractable.reconstruct] at hrecon
  -- Macro for each op case: unfold reconstruct, split on children, subst, use children
  cases op with
  | sbox d c =>
    simp only [reconstructCrypto] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, CryptoExpr.eval, NodeSemantics.evalOp, evalCryptoOpSem]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, CryptoOp.children,
               List.getElem_cons_zero] at h0
    rw [h0]
  | linear b c =>
    simp only [reconstructCrypto] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, CryptoExpr.eval, NodeSemantics.evalOp, evalCryptoOpSem]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, CryptoOp.children,
               List.getElem_cons_zero] at h0
    rw [h0]
  | xor l r =>
    simp only [reconstructCrypto] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, CryptoExpr.eval, NodeSemantics.evalOp, evalCryptoOpSem]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    have h1 := hchildren 1 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, CryptoOp.children,
               List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
    rw [h0, h1]
  | round d b c =>
    simp only [reconstructCrypto] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, CryptoExpr.eval, NodeSemantics.evalOp, evalCryptoOpSem]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, CryptoOp.children,
               List.getElem_cons_zero] at h0
    rw [h0]
  | compose f s =>
    simp only [reconstructCrypto] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, CryptoExpr.eval, NodeSemantics.evalOp, evalCryptoOpSem]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    have h1 := hchildren 1 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, CryptoOp.children,
               List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
    rw [h0, h1]
  | parallel l r =>
    simp only [reconstructCrypto] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, CryptoExpr.eval, NodeSemantics.evalOp, evalCryptoOpSem]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    have h1 := hchildren 1 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, CryptoOp.children,
               List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
    rw [h0, h1]
  | iterate n b =>
    simp only [reconstructCrypto] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, CryptoExpr.eval, NodeSemantics.evalOp, evalCryptoOpSem]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, CryptoOp.children,
               List.getElem_cons_zero] at h0
    rw [h0]
  | const val =>
    simp only [reconstructCrypto] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp [EvalExpr.evalExpr, CryptoExpr.eval, NodeSemantics.evalOp, evalCryptoOpSem]
  | spnBlock r s l =>
    simp only [reconstructCrypto] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, CryptoExpr.eval, NodeSemantics.evalOp, evalCryptoOpSem]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    have h1 := hchildren 1 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, CryptoOp.children,
               List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
    rw [h0, h1]
  | feistelBlock r f =>
    simp only [reconstructCrypto] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, CryptoExpr.eval, NodeSemantics.evalOp, evalCryptoOpSem]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, CryptoOp.children,
               List.getElem_cons_zero] at h0
    rw [h0]
  | spongeBlock rt cap p =>
    simp only [reconstructCrypto] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, CryptoExpr.eval, NodeSemantics.evalOp, evalCryptoOpSem]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, CryptoOp.children,
               List.getElem_cons_zero] at h0
    rw [h0]
  | arxBlock r a rot x =>
    simp only [reconstructCrypto] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, CryptoExpr.eval, NodeSemantics.evalOp, evalCryptoOpSem]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    have h1 := hchildren 1 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    have h2 := hchildren 2 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, CryptoOp.children,
               List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2
    rw [h0, h1, h2]

-- ============================================================
-- Cost function
-- ============================================================

/-- Cost function for extraction: uses localCost from NodeOps. -/
def cryptoCostFn (node : ENode CryptoOp) : Nat :=
  CryptoOp.localCost node.op

-- Smoke tests
#eval reconstructCrypto (.sbox 7 0) [.const 3] |>.isSome          -- true
#eval reconstructCrypto (.compose 0 0) [.const 1, .const 2] |>.isSome -- true
#eval reconstructCrypto (.const 42) [] |>.isSome                    -- true
#eval reconstructCrypto (.sbox 7 0) [] |>.isSome                    -- false

/-- v2.9.1 Fix 5: reconstructCrypto succeeds for all 12 CryptoOp constructors
    when the children list has the correct length (matching CryptoOp.children).
    This proves the hrecon hypothesis of extractAuto_complete. -/
theorem reconstructCrypto_total (op : CryptoOp) (children : List CryptoExpr)
    (h : children.length = (CryptoOp.children op).length) :
    (reconstructCrypto op children).isSome = true := by
  match op, children, h with
  | .sbox _ _, [_], _ => rfl
  | .linear _ _, [_], _ => rfl
  | .xor _ _, [_, _], _ => rfl
  | .round _ _ _, [_], _ => rfl
  | .compose _ _, [_, _], _ => rfl
  | .parallel _ _, [_, _], _ => rfl
  | .iterate _ _, [_], _ => rfl
  | .const _, [], _ => rfl
  | .spnBlock _ _ _, [_, _], _ => rfl
  | .feistelBlock _ _, [_], _ => rfl
  | .spongeBlock _ _ _, [_], _ => rfl
  | .arxBlock _ _ _ _, [_, _, _], _ => rfl

-- ============================================================
-- CryptoSemantics evaluation for CryptoExpr
-- ============================================================

/-- Evaluate a CryptoExpr in the CryptoSemantics domain.
    Mirrors CryptoExpr.eval but computes real crypto metrics
    via evalCryptoOpCS-compatible semantics.
    env maps external variable IDs to CryptoSemantics values. -/
def CryptoExpr.evalCS (e : CryptoExpr) (env : Nat → CryptoSemantics) : CryptoSemantics :=
  match e with
  | .sbox d c =>
    let child := c.evalCS env
    { algebraicDegree := d * child.algebraicDegree
      differentialUniformity := child.differentialUniformity
      linearBias := child.linearBias
      branchNumber := child.branchNumber
      activeMinSboxes := child.activeMinSboxes + 1
      latency := child.latency + 1
      gateCount := child.gateCount + d
      circuitDepth := child.circuitDepth + 1 }
  | .linear bn c =>
    let child := c.evalCS env
    { algebraicDegree := child.algebraicDegree
      differentialUniformity := child.differentialUniformity
      linearBias := child.linearBias
      branchNumber := bn
      activeMinSboxes := child.activeMinSboxes
      latency := child.latency + 1
      gateCount := child.gateCount + bn
      circuitDepth := child.circuitDepth + 1 }
  | .xor l r =>
    let vl := l.evalCS env; let vr := r.evalCS env
    { algebraicDegree := max vl.algebraicDegree vr.algebraicDegree
      differentialUniformity := max vl.differentialUniformity vr.differentialUniformity
      linearBias := max vl.linearBias vr.linearBias
      branchNumber := min vl.branchNumber vr.branchNumber
      activeMinSboxes := max vl.activeMinSboxes vr.activeMinSboxes
      latency := max vl.latency vr.latency + 1
      gateCount := vl.gateCount + vr.gateCount + 1
      circuitDepth := max vl.circuitDepth vr.circuitDepth + 1 }
  | .round d bn c =>
    let child := c.evalCS env
    { algebraicDegree := d * child.algebraicDegree
      differentialUniformity := child.differentialUniformity
      linearBias := child.linearBias
      branchNumber := bn
      activeMinSboxes := child.activeMinSboxes + 1
      latency := child.latency + 2
      gateCount := child.gateCount + d + bn
      circuitDepth := child.circuitDepth + 2 }
  | .compose f s =>
    let vf := f.evalCS env; let vs := s.evalCS env
    { algebraicDegree := vf.algebraicDegree * vs.algebraicDegree
      differentialUniformity := vf.differentialUniformity * vs.differentialUniformity
      -- Piling-Up Lemma (Matsui 1993): product bound for sequential composition
      linearBias := vf.linearBias * vs.linearBias
      branchNumber := min vf.branchNumber vs.branchNumber
      activeMinSboxes := vf.activeMinSboxes + vs.activeMinSboxes
      latency := vf.latency + vs.latency
      gateCount := vf.gateCount + vs.gateCount
      circuitDepth := vf.circuitDepth + vs.circuitDepth }
  | .parallel l r =>
    let vl := l.evalCS env; let vr := r.evalCS env
    { algebraicDegree := max vl.algebraicDegree vr.algebraicDegree
      differentialUniformity := max vl.differentialUniformity vr.differentialUniformity
      linearBias := max vl.linearBias vr.linearBias
      branchNumber := min vl.branchNumber vr.branchNumber
      activeMinSboxes := vl.activeMinSboxes + vr.activeMinSboxes
      latency := max vl.latency vr.latency
      gateCount := vl.gateCount + vr.gateCount
      circuitDepth := max vl.circuitDepth vr.circuitDepth }
  | .iterate n b =>
    let body := b.evalCS env
    { algebraicDegree := safePow body.algebraicDegree n
      -- Consistent with compose: iterate(n, f) = compose(f, ..., f) n times
      differentialUniformity := safePow body.differentialUniformity n
      linearBias := safePow body.linearBias n
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
  | .var id => env id
  | .spnBlock r s l =>
    let vs := s.evalCS env; let vl := l.evalCS env
    { algebraicDegree := safePow (vs.algebraicDegree * vl.algebraicDegree) r
      differentialUniformity := max vs.differentialUniformity vl.differentialUniformity
      linearBias := max vs.linearBias vl.linearBias
      branchNumber := vl.branchNumber
      activeMinSboxes := vl.branchNumber * r
      latency := r * (vs.latency + vl.latency)
      gateCount := r * (vs.gateCount + vl.gateCount)
      circuitDepth := r * (vs.circuitDepth + vl.circuitDepth) }
  | .feistelBlock r f =>
    let vf := f.evalCS env
    { algebraicDegree := safePow vf.algebraicDegree r
      differentialUniformity := vf.differentialUniformity
      linearBias := vf.linearBias
      branchNumber := vf.branchNumber
      activeMinSboxes := r * vf.activeMinSboxes
      latency := r * vf.latency
      gateCount := r * vf.gateCount
      circuitDepth := r * vf.circuitDepth }
  | .spongeBlock rt cap p =>
    let vp := p.evalCS env
    { algebraicDegree := safePow vp.algebraicDegree rt
      -- Capacity isolation: δ_eff = min(perm δ, 2^cap).
      -- This is a SINGLE-QUERY bound (q=1). For q queries: min(δ, q²/2^c).
      -- Source: Bertoni et al. 2008, "On the indifferentiability of the sponge construction"
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
    let va := a.evalCS env; let vrot := rot.evalCS env; let vx := x.evalCS env
    { algebraicDegree := safePow (va.algebraicDegree + vrot.algebraicDegree + vx.algebraicDegree) r
      differentialUniformity := max va.differentialUniformity (max vrot.differentialUniformity vx.differentialUniformity)
      linearBias := max va.linearBias (max vrot.linearBias vx.linearBias)
      branchNumber := min va.branchNumber (min vrot.branchNumber vx.branchNumber)
      activeMinSboxes := r * (va.activeMinSboxes + vrot.activeMinSboxes + vx.activeMinSboxes)
      latency := r * (va.latency + vrot.latency + vx.latency)
      gateCount := r * (va.gateCount + vrot.gateCount + vx.gateCount)
      circuitDepth := r * (va.circuitDepth + vrot.circuitDepth + vx.circuitDepth) }

instance : EvalExpr CryptoExpr CryptoSemantics where
  evalExpr := CryptoExpr.evalCS

-- ============================================================
-- ExtractableSound for CryptoSemantics
-- ============================================================

/-- ExtractableSound for CryptoOp/CryptoExpr/CryptoSemantics.
    Bridges extracted CryptoExpr evaluation (via evalCS) to
    e-graph NodeSemantics evaluation (via evalCryptoOpCS).
    Same 12-case proof structure as crypto_extractable_sound (Nat version). -/
theorem crypto_extractable_sound_cs : ExtractableSound CryptoOp CryptoExpr CryptoSemantics := by
  intro op childExprs expr env v hrecon hlen hchildren
  simp only [Extractable.reconstruct] at hrecon
  cases op with
  | sbox d c =>
    simp only [reconstructCrypto] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, CryptoExpr.evalCS, NodeSemantics.evalOp, evalCryptoOpCS]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, CryptoOp.children,
               List.getElem_cons_zero] at h0
    rw [h0]
  | linear b c =>
    simp only [reconstructCrypto] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, CryptoExpr.evalCS, NodeSemantics.evalOp, evalCryptoOpCS]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, CryptoOp.children,
               List.getElem_cons_zero] at h0
    rw [h0]
  | xor l r =>
    simp only [reconstructCrypto] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, CryptoExpr.evalCS, NodeSemantics.evalOp, evalCryptoOpCS]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    have h1 := hchildren 1 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, CryptoOp.children,
               List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
    rw [h0, h1]
  | round d b c =>
    simp only [reconstructCrypto] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, CryptoExpr.evalCS, NodeSemantics.evalOp, evalCryptoOpCS]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, CryptoOp.children,
               List.getElem_cons_zero] at h0
    rw [h0]
  | compose f s =>
    simp only [reconstructCrypto] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, CryptoExpr.evalCS, NodeSemantics.evalOp, evalCryptoOpCS]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    have h1 := hchildren 1 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, CryptoOp.children,
               List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
    rw [h0, h1]
  | parallel l r =>
    simp only [reconstructCrypto] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, CryptoExpr.evalCS, NodeSemantics.evalOp, evalCryptoOpCS]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    have h1 := hchildren 1 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, CryptoOp.children,
               List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
    rw [h0, h1]
  | iterate n b =>
    simp only [reconstructCrypto] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, CryptoExpr.evalCS, NodeSemantics.evalOp, evalCryptoOpCS]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, CryptoOp.children,
               List.getElem_cons_zero] at h0
    rw [h0]
  | const val =>
    simp only [reconstructCrypto] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp [EvalExpr.evalExpr, CryptoExpr.evalCS, NodeSemantics.evalOp, evalCryptoOpCS]
  | spnBlock r s l =>
    simp only [reconstructCrypto] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, CryptoExpr.evalCS, NodeSemantics.evalOp, evalCryptoOpCS]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    have h1 := hchildren 1 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, CryptoOp.children,
               List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
    rw [h0, h1]
  | feistelBlock r f =>
    simp only [reconstructCrypto] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, CryptoExpr.evalCS, NodeSemantics.evalOp, evalCryptoOpCS]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, CryptoOp.children,
               List.getElem_cons_zero] at h0
    rw [h0]
  | spongeBlock rt cap p =>
    simp only [reconstructCrypto] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, CryptoExpr.evalCS, NodeSemantics.evalOp, evalCryptoOpCS]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, CryptoOp.children,
               List.getElem_cons_zero] at h0
    rw [h0]
  | arxBlock r a rot x =>
    simp only [reconstructCrypto] at hrecon
    split at hrecon <;> simp at hrecon; subst hrecon
    simp only [EvalExpr.evalExpr, CryptoExpr.evalCS, NodeSemantics.evalOp, evalCryptoOpCS]
    have h0 := hchildren 0 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    have h1 := hchildren 1 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    have h2 := hchildren 2 (by simp) (by simp [NodeOps.children, CryptoOp.children])
    simp only [EvalExpr.evalExpr, NodeOps.children, CryptoOp.children,
               List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2
    rw [h0, h1, h2]

-- Smoke tests for CryptoSemantics evaluation
#eval CryptoExpr.evalCS (.sbox 7 (.const 1)) (fun _ => default)
-- Expected: {deg=7, δ=0, ε=0, BN=0, active=1, lat=1, gates=7}

#eval CryptoExpr.evalCS (.compose (.sbox 7 (.const 1)) (.linear 5 (.const 1))) (fun _ => default)
-- Expected: degree = 7*1 = 7, then compose multiplies degrees

end SuperHash
