import SuperHash.CryptoNodeOps

/-!
# SuperHash.Attack.AttackOp — Attack operations for Red Team E-graph

Defines the attack-side node operations used by the E-graph engine to
explore the cryptanalytic design space. Mirrors CryptoOp/CryptoNodeOps
for the Blue Team.

## AttackClass
Five major attack families: differential, linear, algebraic, structural, hybrid.

## AttackOp
Twenty constructors representing composable cryptanalytic building blocks (v4.5.4).
Each child field is a `Nat` (E-class id) referencing another node
in the E-graph.

## NodeOps instance
Full `NodeOps AttackOp` with children, mapChildren, replaceChildren,
localCost, and all four law proofs (zero sorry).
-/

namespace SuperHash

-- ============================================================
-- Section 1: Attack classification
-- ============================================================

/-- Major families of cryptanalytic attacks.
    Classification follows Biryukov & Nikolic (2010). -/
inductive AttackClass where
  | differential
  | linear
  | algebraic
  | structural
  | hybrid
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited

-- ============================================================
-- Section 2: AttackOp — E-graph node operations
-- ============================================================

/-- E-graph node operations for cryptanalytic attack composition.
    Twenty constructors representing composable cryptanalytic building blocks.
    Each child field is a `Nat` (E-class id) referencing another node
    in the E-graph.
    Convention: metadata parameters first, then E-class id children.
    v4.5.4: added slideAttack, integralAttack, cubeAttack,
    zeroSumPartition, invariantSubspace, divisionProperty. -/
inductive AttackOp where
  -- Differential family
  | diffChar (prob : Nat) (child : Nat)
  | truncatedDiff (activeBytes : Nat) (child : Nat)
  | boomerang (child1 child2 : Nat)
  | impossible (rounds : Nat) (child : Nat)
  -- Linear family
  | linearTrail (bias : Nat) (child : Nat)
  | linearHull (numTrails : Nat) (child : Nat)
  -- Algebraic family
  | algebraicRelation (degree : Nat) (child : Nat)
  | grobnerStep (child : Nat)
  -- Structural family
  | meetInMiddle (splitRound : Nat) (child1 child2 : Nat)
  | rebound (inRounds outRounds : Nat) (child : Nat)
  -- Composition (reuse E-graph)
  | compose (first second : Nat)
  | parallel (left right : Nat)
  | iterate (n : Nat) (body : Nat)
  | const (cost : Nat)
  -- v4.5.4: Advanced attack models (adapted from TrustHash v5.0)
  | slideAttack (period : Nat) (child : Nat)
  | integralAttack (distinguisherDim : Nat) (child : Nat)
  | cubeAttack (cubeDim : Nat) (child : Nat)
  | zeroSumPartition (partitionDim : Nat) (child : Nat)
  | invariantSubspace (basisSize : Nat) (child : Nat)
  | divisionProperty (blockSize : Nat) (child : Nat)
  deriving Repr, DecidableEq, Hashable

/-- BEq via DecidableEq (ensures LawfulBEq compatibility). -/
instance : BEq AttackOp where
  beq x y := decide (x = y)

instance : LawfulBEq AttackOp where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true_eq.mpr rfl

instance : Inhabited AttackOp where
  default := .const 0

instance : LawfulHashable AttackOp where
  hash_eq {a b} h := by
    have := eq_of_beq h
    subst this; rfl

-- Smoke tests
#eval AttackOp.diffChar 10 0 == AttackOp.diffChar 10 0      -- true
#eval AttackOp.diffChar 10 0 == AttackOp.diffChar 5 0       -- false
#eval AttackOp.const 42 == AttackOp.const 42                 -- true
#eval AttackOp.boomerang 0 1 == AttackOp.parallel 0 1       -- false
#eval AttackOp.meetInMiddle 5 0 1 == AttackOp.meetInMiddle 5 0 1 -- true
#eval AttackOp.rebound 3 4 0 == AttackOp.rebound 3 4 0      -- true

-- ============================================================
-- Section 3: NodeOps functions
-- ============================================================

/-- Extract children (E-class IDs) from an AttackOp. -/
def AttackOp.children : AttackOp → List EClassId
  | .diffChar _ c => [c]
  | .truncatedDiff _ c => [c]
  | .boomerang c1 c2 => [c1, c2]
  | .impossible _ c => [c]
  | .linearTrail _ c => [c]
  | .linearHull _ c => [c]
  | .algebraicRelation _ c => [c]
  | .grobnerStep c => [c]
  | .meetInMiddle _ c1 c2 => [c1, c2]
  | .rebound _ _ c => [c]
  | .compose f s => [f, s]
  | .parallel l r => [l, r]
  | .iterate _ b => [b]
  | .const _ => []
  | .slideAttack _ c => [c]
  | .integralAttack _ c => [c]
  | .cubeAttack _ c => [c]
  | .zeroSumPartition _ c => [c]
  | .invariantSubspace _ c => [c]
  | .divisionProperty _ c => [c]

/-- Apply a function to all child E-class IDs. -/
def AttackOp.mapChildren (f : EClassId → EClassId) : AttackOp → AttackOp
  | .diffChar p c => .diffChar p (f c)
  | .truncatedDiff ab c => .truncatedDiff ab (f c)
  | .boomerang c1 c2 => .boomerang (f c1) (f c2)
  | .impossible r c => .impossible r (f c)
  | .linearTrail b c => .linearTrail b (f c)
  | .linearHull n c => .linearHull n (f c)
  | .algebraicRelation d c => .algebraicRelation d (f c)
  | .grobnerStep c => .grobnerStep (f c)
  | .meetInMiddle sr c1 c2 => .meetInMiddle sr (f c1) (f c2)
  | .rebound ir or_ c => .rebound ir or_ (f c)
  | .compose a s => .compose (f a) (f s)
  | .parallel l r => .parallel (f l) (f r)
  | .iterate n b => .iterate n (f b)
  | .const v => .const v
  | .slideAttack p c => .slideAttack p (f c)
  | .integralAttack d c => .integralAttack d (f c)
  | .cubeAttack d c => .cubeAttack d (f c)
  | .zeroSumPartition d c => .zeroSumPartition d (f c)
  | .invariantSubspace bs c => .invariantSubspace bs (f c)
  | .divisionProperty bs c => .divisionProperty bs (f c)

/-- Replace children positionally. -/
def AttackOp.replaceChildren : AttackOp → List EClassId → AttackOp
  | .diffChar p _, c :: _ => .diffChar p c
  | .truncatedDiff ab _, c :: _ => .truncatedDiff ab c
  | .boomerang _ _, c1 :: c2 :: _ => .boomerang c1 c2
  | .impossible r _, c :: _ => .impossible r c
  | .linearTrail b _, c :: _ => .linearTrail b c
  | .linearHull n _, c :: _ => .linearHull n c
  | .algebraicRelation d _, c :: _ => .algebraicRelation d c
  | .grobnerStep _, c :: _ => .grobnerStep c
  | .meetInMiddle sr _ _, c1 :: c2 :: _ => .meetInMiddle sr c1 c2
  | .rebound ir or_ _, c :: _ => .rebound ir or_ c
  | .compose _ _, a :: s :: _ => .compose a s
  | .parallel _ _, l :: r :: _ => .parallel l r
  | .iterate n _, b :: _ => .iterate n b
  | .const v, _ => .const v
  | .slideAttack p _, c :: _ => .slideAttack p c
  | .integralAttack d _, c :: _ => .integralAttack d c
  | .cubeAttack d _, c :: _ => .cubeAttack d c
  | .zeroSumPartition d _, c :: _ => .zeroSumPartition d c
  | .invariantSubspace bs _, c :: _ => .invariantSubspace bs c
  | .divisionProperty bs _, c :: _ => .divisionProperty bs c
  | op, _ => op  -- fallback: return unchanged

/-- Local cost of an AttackOp (not including children). -/
def AttackOp.localCost : AttackOp → Nat
  | .diffChar p _ => p          -- higher probability → more expensive analysis
  | .truncatedDiff ab _ => ab   -- active bytes as cost
  | .boomerang _ _ => 2         -- boomerang needs two differentials
  | .impossible r _ => r        -- rounds of impossible path
  | .linearTrail b _ => b       -- bias as cost
  | .linearHull n _ => n        -- number of trails to aggregate
  | .algebraicRelation d _ => d -- degree of relation
  | .grobnerStep _ => 3         -- Grobner basis step is expensive
  | .meetInMiddle sr _ _ => sr  -- split round as cost
  | .rebound ir or_ _ => ir + or_ -- total rounds covered
  | .compose _ _ => 0           -- composition is free
  | .parallel _ _ => 0          -- parallel is free
  | .iterate n _ => n           -- cost proportional to iterations
  | .const _ => 0
  | .slideAttack period _ => period          -- slide period as cost
  | .integralAttack dim _ => dim             -- distinguisher dimension
  | .cubeAttack dim _ => dim                 -- cube dimension
  | .zeroSumPartition dim _ => dim           -- partition dimension
  | .invariantSubspace bs _ => bs            -- basis size
  | .divisionProperty bs _ => bs             -- block size

-- ============================================================
-- Section 4: Law proofs
-- ============================================================

private theorem mapChildren_children_proof (f : EClassId → EClassId) (op : AttackOp) :
    (op.mapChildren f).children = op.children.map f := by
  cases op <;> simp [AttackOp.mapChildren, AttackOp.children, List.map]

private theorem mapChildren_id_proof (op : AttackOp) :
    AttackOp.mapChildren id op = op := by
  cases op <;> simp [AttackOp.mapChildren]

private theorem replaceChildren_children_proof (op : AttackOp) (ids : List EClassId)
    (h : ids.length = op.children.length) :
    (op.replaceChildren ids).children = ids := by
  match op, ids, h with
  | .diffChar p _, [c], _ => rfl
  | .truncatedDiff ab _, [c], _ => rfl
  | .boomerang _ _, [c1, c2], _ => rfl
  | .impossible r _, [c], _ => rfl
  | .linearTrail b _, [c], _ => rfl
  | .linearHull n _, [c], _ => rfl
  | .algebraicRelation d _, [c], _ => rfl
  | .grobnerStep _, [c], _ => rfl
  | .meetInMiddle sr _ _, [c1, c2], _ => rfl
  | .rebound ir or_ _, [c], _ => rfl
  | .compose _ _, [a, s], _ => rfl
  | .parallel _ _, [l, r], _ => rfl
  | .iterate n _, [b], _ => rfl
  | .const v, [], _ => rfl
  | .slideAttack p _, [c], _ => rfl
  | .integralAttack d _, [c], _ => rfl
  | .cubeAttack d _, [c], _ => rfl
  | .zeroSumPartition d _, [c], _ => rfl
  | .invariantSubspace bs _, [c], _ => rfl
  | .divisionProperty bs _, [c], _ => rfl

private theorem replaceChildren_sameShape_proof (op : AttackOp) (ids : List EClassId)
    (h : ids.length = op.children.length) :
    AttackOp.mapChildren (fun _ => (0 : EClassId)) (op.replaceChildren ids) =
      AttackOp.mapChildren (fun _ => (0 : EClassId)) op := by
  match op, ids, h with
  | .diffChar p _, [c], _ => rfl
  | .truncatedDiff ab _, [c], _ => rfl
  | .boomerang _ _, [c1, c2], _ => rfl
  | .impossible r _, [c], _ => rfl
  | .linearTrail b _, [c], _ => rfl
  | .linearHull n _, [c], _ => rfl
  | .algebraicRelation d _, [c], _ => rfl
  | .grobnerStep _, [c], _ => rfl
  | .meetInMiddle sr _ _, [c1, c2], _ => rfl
  | .rebound ir or_ _, [c], _ => rfl
  | .compose _ _, [a, s], _ => rfl
  | .parallel _ _, [l, r], _ => rfl
  | .iterate n _, [b], _ => rfl
  | .const v, [], _ => rfl
  | .slideAttack p _, [c], _ => rfl
  | .integralAttack d _, [c], _ => rfl
  | .cubeAttack d _, [c], _ => rfl
  | .zeroSumPartition d _, [c], _ => rfl
  | .invariantSubspace bs _, [c], _ => rfl
  | .divisionProperty bs _, [c], _ => rfl

instance : NodeOps AttackOp where
  children := AttackOp.children
  mapChildren := AttackOp.mapChildren
  replaceChildren := AttackOp.replaceChildren
  localCost := AttackOp.localCost
  mapChildren_children := mapChildren_children_proof
  mapChildren_id := mapChildren_id_proof
  replaceChildren_children := replaceChildren_children_proof
  replaceChildren_sameShape := replaceChildren_sameShape_proof

-- ============================================================
-- Section 5: Smoke tests
-- ============================================================

#eval AttackOp.children (.diffChar 10 42)           -- [42]
#eval AttackOp.children (.boomerang 10 20)          -- [10, 20]
#eval AttackOp.children (.const 99)                 -- []
#eval AttackOp.children (.meetInMiddle 5 0 1)       -- [0, 1]
#eval AttackOp.children (.rebound 3 4 0)            -- [0]
#eval AttackOp.mapChildren (· + 100) (.boomerang 1 2)  -- boomerang 101 102
#eval AttackOp.mapChildren (· + 100) (.meetInMiddle 5 0 1)  -- meetInMiddle 5 100 101

-- v4.5.4 smoke tests
#eval AttackOp.children (.slideAttack 5 42)          -- [42]
#eval AttackOp.children (.integralAttack 8 10)       -- [10]
#eval AttackOp.children (.zeroSumPartition 12 3)     -- [3]

end SuperHash
