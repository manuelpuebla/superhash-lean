import SuperHash.CryptoOp

/-!
# SuperHash.CryptoNodeOps — NodeOps typeclass and CryptoOp instance

Defines the generic `NodeOps` typeclass for E-graph node operations
and instantiates it for `CryptoOp`. Also provides `evalCryptoOp`
for concrete evaluation.

Adapted from OptiSat (LambdaSat.Core).
-/

namespace SuperHash

/-- E-class identifier (index into the E-graph). -/
abbrev EClassId := Nat

/-- Typeclass for E-graph node operations.
    Any domain-specific node type must implement this interface. -/
class NodeOps (Op : Type) where
  children : Op → List EClassId
  mapChildren : (EClassId → EClassId) → Op → Op
  replaceChildren : Op → List EClassId → Op
  localCost : Op → Nat
  mapChildren_children : ∀ (f : EClassId → EClassId) (op : Op),
    children (mapChildren f op) = (children op).map f
  mapChildren_id : ∀ (op : Op), mapChildren id op = op
  replaceChildren_children : ∀ (op : Op) (ids : List EClassId),
    ids.length = (children op).length →
    children (replaceChildren op ids) = ids
  replaceChildren_sameShape : ∀ (op : Op) (ids : List EClassId),
    ids.length = (children op).length →
    mapChildren (fun _ => (0 : EClassId)) (replaceChildren op ids) =
      mapChildren (fun _ => (0 : EClassId)) op

/-- Extract children (E-class IDs) from a CryptoOp. -/
def CryptoOp.children : CryptoOp → List EClassId
  | .sbox _ c => [c]
  | .linear _ c => [c]
  | .xor l r => [l, r]
  | .round _ _ c => [c]
  | .compose f s => [f, s]
  | .parallel l r => [l, r]
  | .iterate _ b => [b]
  | .const _ => []
  | .spnBlock _ s l => [s, l]
  | .feistelBlock _ f => [f]
  | .spongeBlock _ _ p => [p]
  | .arxBlock _ a r x => [a, r, x]

/-- Apply a function to all child E-class IDs. -/
def CryptoOp.mapChildren (f : EClassId → EClassId) : CryptoOp → CryptoOp
  | .sbox d c => .sbox d (f c)
  | .linear b c => .linear b (f c)
  | .xor l r => .xor (f l) (f r)
  | .round d b c => .round d b (f c)
  | .compose a s => .compose (f a) (f s)
  | .parallel l r => .parallel (f l) (f r)
  | .iterate n b => .iterate n (f b)
  | .const v => .const v
  | .spnBlock r s l => .spnBlock r (f s) (f l)
  | .feistelBlock r fc => .feistelBlock r (f fc)
  | .spongeBlock rt cap p => .spongeBlock rt cap (f p)
  | .arxBlock r a rot x => .arxBlock r (f a) (f rot) (f x)

/-- Replace children positionally. -/
def CryptoOp.replaceChildren : CryptoOp → List EClassId → CryptoOp
  | .sbox d _, c :: _ => .sbox d c
  | .linear b _, c :: _ => .linear b c
  | .xor _ _, l :: r :: _ => .xor l r
  | .round d b _, c :: _ => .round d b c
  | .compose _ _, a :: s :: _ => .compose a s
  | .parallel _ _, l :: r :: _ => .parallel l r
  | .iterate n _, b :: _ => .iterate n b
  | .const v, _ => .const v
  | .spnBlock r _ _, s :: l :: _ => .spnBlock r s l
  | .feistelBlock r _, f :: _ => .feistelBlock r f
  | .spongeBlock rt cap _, p :: _ => .spongeBlock rt cap p
  | .arxBlock r _ _ _, a :: rot :: x :: _ => .arxBlock r a rot x
  | op, _ => op  -- fallback: return unchanged

/-- Local cost of a CryptoOp (not including children). -/
def CryptoOp.localCost : CryptoOp → Nat
  | .sbox d _ => d        -- higher degree = more expensive
  | .linear b _ => b      -- branch number as cost
  | .xor _ _ => 1
  | .round d b _ => d + b
  | .compose _ _ => 0     -- composition is free
  | .parallel _ _ => 0    -- parallel is free
  | .iterate n _ => n     -- cost proportional to iterations
  | .const _ => 0
  | .spnBlock r _ _ => r      -- cost proportional to rounds
  | .feistelBlock r _ => r
  | .spongeBlock rt cap _ => rt + cap
  | .arxBlock r _ _ _ => r

-- ============================================================
-- Law proofs
-- ============================================================

private theorem mapChildren_children_proof (f : EClassId → EClassId) (op : CryptoOp) :
    (op.mapChildren f).children = op.children.map f := by
  cases op <;> simp [CryptoOp.mapChildren, CryptoOp.children, List.map]

private theorem mapChildren_id_proof (op : CryptoOp) :
    CryptoOp.mapChildren id op = op := by
  cases op <;> simp [CryptoOp.mapChildren]

private theorem replaceChildren_children_proof (op : CryptoOp) (ids : List EClassId)
    (h : ids.length = op.children.length) :
    (op.replaceChildren ids).children = ids := by
  match op, ids, h with
  | .sbox d _, [c], _ => rfl
  | .linear b _, [c], _ => rfl
  | .xor _ _, [l, r], _ => rfl
  | .round d b _, [c], _ => rfl
  | .compose _ _, [a, s], _ => rfl
  | .parallel _ _, [l, r], _ => rfl
  | .iterate n _, [b], _ => rfl
  | .const v, [], _ => rfl
  | .spnBlock r _ _, [s, l], _ => rfl
  | .feistelBlock r _, [f], _ => rfl
  | .spongeBlock rt cap _, [p], _ => rfl
  | .arxBlock r _ _ _, [a, rot, x], _ => rfl

private theorem replaceChildren_sameShape_proof (op : CryptoOp) (ids : List EClassId)
    (h : ids.length = op.children.length) :
    CryptoOp.mapChildren (fun _ => (0 : EClassId)) (op.replaceChildren ids) =
      CryptoOp.mapChildren (fun _ => (0 : EClassId)) op := by
  match op, ids, h with
  | .sbox d _, [c], _ => rfl
  | .linear b _, [c], _ => rfl
  | .xor _ _, [l, r], _ => rfl
  | .round d b _, [c], _ => rfl
  | .compose _ _, [a, s], _ => rfl
  | .parallel _ _, [l, r], _ => rfl
  | .iterate n _, [b], _ => rfl
  | .const v, [], _ => rfl
  | .spnBlock r _ _, [s, l], _ => rfl
  | .feistelBlock r _, [f], _ => rfl
  | .spongeBlock rt cap _, [p], _ => rfl
  | .arxBlock r _ _ _, [a, rot, x], _ => rfl

instance : NodeOps CryptoOp where
  children := CryptoOp.children
  mapChildren := CryptoOp.mapChildren
  replaceChildren := CryptoOp.replaceChildren
  localCost := CryptoOp.localCost
  mapChildren_children := mapChildren_children_proof
  mapChildren_id := mapChildren_id_proof
  replaceChildren_children := replaceChildren_children_proof
  replaceChildren_sameShape := replaceChildren_sameShape_proof

-- ============================================================
-- Concrete evaluation
-- ============================================================

/-- Evaluate a CryptoOp given child values.
    Abstract security metric computation: Val = Nat.
    Block semantics compose from primitives:
    - spnBlock(r, s, l) = r * (s + l)  ≈ iterate(r, compose(sbox, linear))
    - feistelBlock(r, f) = r * f        ≈ iterate(r, compose(f, xor))
    - spongeBlock(rt, cap, p) = rt * p + cap  ≈ absorption + squeezing
    - arxBlock(r, a, rot, x) = r * (a + rot + x)  ≈ iterate(r, add+rotate+xor) -/
def evalCryptoOp : CryptoOp → List Nat → Nat
  | .sbox d _, [v] => d * v          -- degree amplification
  | .linear b _, [v] => b + v        -- linear mixing
  | .xor _ _, [l, r] => l + r        -- XOR combines
  | .round d b _, [v] => d * v + b   -- round = sbox + linear
  | .compose _ _, [f, s] => f + s    -- sequential composition
  | .parallel _ _, [l, r] => l + r   -- parallel combination
  | .iterate n _, [v] => n * v       -- iterated composition
  | .const v, [] => v                -- constant value
  | .spnBlock r _ _, [s, l] => r * (s + l)       -- SPN: rounds × (sbox + linear)
  | .feistelBlock r _, [f] => r * f              -- Feistel: rounds × round function
  | .spongeBlock rt cap _, [p] => rt * p + cap   -- Sponge: absorption + capacity
  | .arxBlock r _ _ _, [a, rot, x] => r * (a + rot + x) -- ARX: rounds × (add+rotate+xor)
  | _, _ => 0                        -- fallback

-- Smoke tests (v1.0)
#eval CryptoOp.children (.round 7 5 42)          -- [42]
#eval CryptoOp.children (.xor 10 20)             -- [10, 20]
#eval CryptoOp.children (.const 99)              -- []
#eval CryptoOp.mapChildren (· + 100) (.xor 1 2)  -- xor 101 102
#eval evalCryptoOp (.sbox 7 0) [10]              -- 70
#eval evalCryptoOp (.round 7 5 0) [10]           -- 75
#eval evalCryptoOp (.iterate 10 0) [8]           -- 80

-- Smoke tests (v2.0 blocks)
#eval CryptoOp.children (.spnBlock 10 0 1)       -- [0, 1]
#eval CryptoOp.children (.feistelBlock 16 0)     -- [0]
#eval CryptoOp.children (.spongeBlock 8 4 0)     -- [0]
#eval CryptoOp.children (.arxBlock 20 0 1 2)     -- [0, 1, 2]
#eval evalCryptoOp (.spnBlock 10 0 1) [7, 5]     -- 10 * (7 + 5) = 120
#eval evalCryptoOp (.feistelBlock 16 0) [3]      -- 16 * 3 = 48
#eval evalCryptoOp (.spongeBlock 8 4 0) [5]      -- 8 * 5 + 4 = 44
#eval evalCryptoOp (.arxBlock 20 0 1 2) [2, 3, 1] -- 20 * (2 + 3 + 1) = 120

end SuperHash
