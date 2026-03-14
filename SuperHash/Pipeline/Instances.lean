import SuperHash.Pipeline.Extract
import SuperHash.Rules.CryptoRules

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

end SuperHash
