import SuperHash.EGraph.Consistency
import SuperHash.EGraph.AddNodeTriple

/-!
# SuperHash.EGraph.Tests — NodeSemantics instance + smoke tests

Instantiates `NodeSemantics CryptoOp Nat` and provides smoke tests
for the E-graph engine with crypto operations.

## Semantic Model: Nat Semiring

The semantic domain `Val = Nat` is an intentional design choice. The rewrite rules
(roundCompose, iterateOne, composeAssoc, parallelIdentity, iterateCompose) rely on
**semiring identities**:
- `1 * x = x` (iterateOne)
- `x + 0 = x` (parallelIdentity)
- `(a + b) + c = a + (b + c)` (composeAssoc)
- `a * (b * c) = (a * b) * c` (iterateCompose)
- `d * x + b = d * x + b` (roundCompose — structural)

**Known limitation**: `xor`, `compose`, and `parallel` all map to Nat addition (`v l + v r`).
This means the model cannot distinguish these three operations semantically — a rule
swapping `xor` for `compose` would be accepted as "sound" under this model. However,
all current rules preserve the correct CryptoOp constructors structurally, and the
E-graph maintains structural identity of operations. The Nat model validates the
algebraic equivalences that the rules actually use.

A richer semantic domain (e.g., a free algebra or SecurityMetrics) could distinguish
these operations but would break existing rules that depend on Nat semiring laws.
-/

set_option linter.unusedSimpArgs false

namespace SuperHash

/-- Evaluate a CryptoOp given an environment and value mapping.
    This wraps `evalCryptoOp` into the NodeSemantics interface. -/
def evalCryptoOpSem (op : CryptoOp) (_env : Nat → Nat) (v : EClassId → Nat) : Nat :=
  match op with
  | .sbox d c => d * v c
  | .linear b c => b + v c
  | .xor l r => v l + v r
  | .round d b c => d * v c + b
  | .compose f s => v f + v s
  | .parallel l r => v l + v r
  | .iterate n b => n * v b
  | .const val => val
  | .spnBlock r s l => r * (v s + v l)
  | .feistelBlock r f => r * v f
  | .spongeBlock rt cap p => rt * v p + cap
  | .arxBlock r a rot x => r * (v a + v rot + v x)

private theorem evalOp_ext_proof (op : CryptoOp) (_env : Nat → Nat)
    (v v' : EClassId → Nat)
    (h : ∀ c ∈ NodeOps.children op, v c = v' c) :
    evalCryptoOpSem op _env v = evalCryptoOpSem op _env v' := by
  cases op <;> simp [evalCryptoOpSem, NodeOps.children, CryptoOp.children] at h ⊢
  all_goals (first
    | (obtain ⟨h1, h2, h3⟩ := h; rw [h1, h2, h3])
    | (obtain ⟨h1, h2⟩ := h; rw [h1, h2])
    | (rw [h])
    | rfl)

private theorem evalOp_mapChildren_proof (f : EClassId → EClassId) (op : CryptoOp)
    (env : Nat → Nat) (v : EClassId → Nat) :
    evalCryptoOpSem (NodeOps.mapChildren f op) env v =
    evalCryptoOpSem op env (fun c => v (f c)) := by
  cases op <;> simp [evalCryptoOpSem, NodeOps.mapChildren, CryptoOp.mapChildren]

private theorem evalOp_skeleton_proof
    (op₁ op₂ : CryptoOp) (env : Nat → Nat) (v₁ v₂ : EClassId → Nat)
    (hskel : NodeOps.mapChildren (fun _ => (0 : EClassId)) op₁ =
             NodeOps.mapChildren (fun _ => (0 : EClassId)) op₂)
    (hvals : ∀ (i : Nat) (h₁ : i < (NodeOps.children op₁).length)
                (h₂ : i < (NodeOps.children op₂).length),
             v₁ ((NodeOps.children op₁)[i]) = v₂ ((NodeOps.children op₂)[i])) :
    evalCryptoOpSem op₁ env v₁ = evalCryptoOpSem op₂ env v₂ := by
  cases op₁ <;> cases op₂ <;>
    simp [NodeOps.mapChildren, CryptoOp.mapChildren] at hskel <;>
    simp [evalCryptoOpSem, NodeOps.children, CryptoOp.children] at hvals ⊢
  -- Close remaining goals by combining hskel + hvals
  all_goals (first
    -- 2-part hskel + 1-child
    | (obtain ⟨rfl, rfl⟩ := hskel; rw [hvals 0 (by omega) (by omega)])
    | (obtain ⟨rfl, rfl⟩ := hskel; rw [hvals])
    -- 1-part hskel + 3-child
    | (obtain rfl := hskel
       have h0 := hvals 0 (by omega) (by omega)
       have h1 := hvals 1 (by omega) (by omega)
       have h2 := hvals 2 (by omega) (by omega)
       simp [List.getElem_cons_succ, List.getElem_cons_zero] at h0 h1 h2
       rw [h0, h1, h2])
    -- 1-part hskel + 2-child
    | (obtain rfl := hskel
       have h0 := hvals 0 (by omega) (by omega)
       have h1 := hvals 1 (by omega) (by omega)
       simp [List.getElem_cons_succ, List.getElem_cons_zero] at h0 h1
       rw [h0, h1])
    -- 1-part hskel + 1-child
    | (obtain rfl := hskel; rw [hvals])
    -- 0-part hskel + 3-child
    | (have h0 := hvals 0 (by omega) (by omega)
       have h1 := hvals 1 (by omega) (by omega)
       have h2 := hvals 2 (by omega) (by omega)
       simp [List.getElem_cons_succ, List.getElem_cons_zero] at h0 h1 h2
       rw [h0, h1, h2])
    -- 0-part hskel + 2-child
    | (have h0 := hvals 0 (by omega) (by omega)
       have h1 := hvals 1 (by omega) (by omega)
       simp [List.getElem_cons_succ, List.getElem_cons_zero] at h0 h1
       rw [h0, h1])
    | exact hskel
    | rfl)

instance : NodeSemantics CryptoOp Nat where
  evalOp := evalCryptoOpSem
  evalOp_ext := evalOp_ext_proof
  evalOp_mapChildren := evalOp_mapChildren_proof
  evalOp_skeleton := evalOp_skeleton_proof

-- ============================================================
-- Smoke tests
-- ============================================================

/-- Empty E-graph is consistent with the default valuation. -/
example : ConsistentValuation (EGraph.empty : EGraph CryptoOp) (fun _ => (0 : Nat)) (fun _ => default) :=
  empty_consistent _

-- Operational smoke tests
open EGraph in
#eval
  let g : EGraph CryptoOp := EGraph.empty
  let (id0, g) := g.add ⟨CryptoOp.const 10⟩
  let (_id1, g) := g.add ⟨CryptoOp.sbox 7 id0⟩
  let (_id2, g) := g.add ⟨CryptoOp.linear 5 id0⟩
  let s := g.stats
  (s.numClasses, s.numNodes, s.unionFindSize)

-- Merge test
open EGraph in
#eval
  let g : EGraph CryptoOp := EGraph.empty
  let (id0, g) := g.add ⟨CryptoOp.const 1⟩
  let (id1, g) := g.add ⟨CryptoOp.const 2⟩
  let g := g.merge id0 id1
  let s := g.stats
  (s.numClasses, s.numNodes, s.unionFindSize)

-- ============================================================
-- Structural distinguishability (A4 documentation)
-- ============================================================

/-- CryptoOp constructors are structurally distinct despite shared Nat semantics. -/
example : CryptoOp.sbox 2 0 ≠ CryptoOp.compose 0 1 := by decide
example : CryptoOp.xor 0 1 ≠ CryptoOp.compose 0 1 := by decide
example : CryptoOp.xor 0 1 ≠ CryptoOp.parallel 0 1 := by decide

/-- Semantic distinguishability: sbox and linear differ on specific inputs.
    sbox 2 0 with v(0)=3: 2*3 = 6; linear 2 0 with v(0)=3: 2+3 = 5. -/
example : evalCryptoOpSem (.sbox 2 0) (fun _ => 0) (fun _ => 3) ≠
          evalCryptoOpSem (.linear 2 0) (fun _ => 0) (fun _ => 3) := by decide

/-- iterate and compose differ: iterate 2 0 with v(0)=3: 2*3=6;
    compose 0 1 with v(0)=3,v(1)=3: 3+3=6 — same here, but... -/
example : evalCryptoOpSem (.iterate 2 0) (fun _ => 0) (fun _ => 3) =
          evalCryptoOpSem (.compose 0 1) (fun _ => 0) (fun _ => 3) := by decide

/-- ...they differ when children have different values: iterate 2 0 with v(0)=3: 6;
    compose 0 1 with v(0)=3,v(1)=5: 3+5=8. -/
example : evalCryptoOpSem (.iterate 2 0) (fun _ => 0) (fun c => if c == 0 then 3 else 5) ≠
          evalCryptoOpSem (.compose 0 1) (fun _ => 0) (fun c => if c == 0 then 3 else 5) := by
  native_decide

end SuperHash
