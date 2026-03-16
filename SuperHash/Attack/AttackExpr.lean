import SuperHash.Attack.AttackNodeSemantics
import SuperHash.Pipeline.Extract

/-!
# SuperHash.Attack.AttackExpr — Attack expression type + extraction instances

Provides:
- `AttackExpr`: inductive mirroring the 14 AttackOp constructors (+ `var` for variables)
- `AttackExpr.eval`: evaluate an AttackExpr in an environment of AttackSemantics
- `Extractable AttackOp AttackExpr`: reconstruct AttackExpr from e-graph nodes
- `EvalExpr AttackExpr AttackSemantics`: evaluate extracted expressions

Follows the same pattern as Pipeline/Instances.lean (CryptoExpr/CryptoOp).
-/

namespace SuperHash

-- ============================================================
-- Section 1: AttackExpr — the expression type
-- ============================================================

/-- Attack expression tree, mirroring AttackOp constructors.
    Each constructor replaces E-class IDs with recursive child expressions.
    `var` provides external inputs (analogous to CryptoExpr.var). -/
inductive AttackExpr where
  -- Differential family
  | diffChar (prob : Nat) (child : AttackExpr)
  | truncatedDiff (activeBytes : Nat) (child : AttackExpr)
  | boomerang (child1 child2 : AttackExpr)
  | impossible (rounds : Nat) (child : AttackExpr)
  -- Linear family
  | linearTrail (bias : Nat) (child : AttackExpr)
  | linearHull (numTrails : Nat) (child : AttackExpr)
  -- Algebraic family
  | algebraicRelation (degree : Nat) (child : AttackExpr)
  | grobnerStep (child : AttackExpr)
  -- Structural family
  | meetInMiddle (splitRound : Nat) (child1 child2 : AttackExpr)
  | rebound (inRounds outRounds : Nat) (child : AttackExpr)
  -- Composition
  | compose (first second : AttackExpr)
  | parallel (left right : AttackExpr)
  | iterate (n : Nat) (body : AttackExpr)
  | const (cost : Nat)
  -- v4.5.4: Advanced attack models
  | slideAttack (period : Nat) (child : AttackExpr)
  | integralAttack (distinguisherDim : Nat) (child : AttackExpr)
  | cubeAttack (cubeDim : Nat) (child : AttackExpr)
  | zeroSumPartition (partitionDim : Nat) (child : AttackExpr)
  | invariantSubspace (basisSize : Nat) (child : AttackExpr)
  | divisionProperty (blockSize : Nat) (child : AttackExpr)
  -- External variable
  | var (id : Nat)

-- ============================================================
-- Section 2: Evaluate AttackExpr in AttackSemantics domain
-- ============================================================

/-- Evaluate an AttackExpr given an environment mapping variable IDs
    to AttackSemantics values. Mirrors evalAttackSem/evalAttackOpAS. -/
def AttackExpr.eval (e : AttackExpr) (env : Nat → AttackSemantics) : AttackSemantics :=
  match e with
  | .diffChar p c =>
    let child := c.eval env
    { timeCost := child.timeCost + 2 * p
      memoryCost := child.memoryCost + p
      dataCost := child.dataCost + p
      successProb := child.successProb + p
      roundsCovered := child.roundsCovered + 1 }
  | .truncatedDiff ab c =>
    let child := c.eval env
    { timeCost := child.timeCost + ab
      memoryCost := child.memoryCost + ab
      dataCost := child.dataCost + ab
      successProb := child.successProb + ab / 2
      roundsCovered := child.roundsCovered + 1 }
  | .boomerang c1 c2 =>
    let v1 := c1.eval env; let v2 := c2.eval env
    { timeCost := v1.timeCost + v2.timeCost + 1
      memoryCost := max v1.memoryCost v2.memoryCost
      dataCost := max v1.dataCost v2.dataCost + 1
      successProb := v1.successProb + v2.successProb
      roundsCovered := v1.roundsCovered + v2.roundsCovered }
  | .impossible r c =>
    let child := c.eval env
    { timeCost := child.timeCost + r
      memoryCost := child.memoryCost + r
      dataCost := child.dataCost
      successProb := child.successProb
      roundsCovered := child.roundsCovered + r }
  | .linearTrail b c =>
    let child := c.eval env
    { timeCost := child.timeCost + 2 * b
      memoryCost := child.memoryCost
      dataCost := child.dataCost + 2 * b
      successProb := child.successProb + b
      roundsCovered := child.roundsCovered + 1 }
  | .linearHull nt c =>
    let child := c.eval env
    { timeCost := child.timeCost + nt
      memoryCost := child.memoryCost + nt
      dataCost := child.dataCost + nt
      successProb := if child.successProb > nt / 2
                     then child.successProb - nt / 2
                     else 0
      roundsCovered := child.roundsCovered + 1 }
  | .algebraicRelation d c =>
    let child := c.eval env
    { timeCost := child.timeCost + d * d
      memoryCost := child.memoryCost + d
      dataCost := child.dataCost
      successProb := child.successProb
      roundsCovered := child.roundsCovered + 1 }
  | .grobnerStep c =>
    let child := c.eval env
    { timeCost := child.timeCost + 3
      memoryCost := child.memoryCost + 3
      dataCost := child.dataCost
      successProb := child.successProb
      roundsCovered := child.roundsCovered }
  | .meetInMiddle sr c1 c2 =>
    let v1 := c1.eval env; let v2 := c2.eval env
    { timeCost := max v1.timeCost v2.timeCost + sr
      memoryCost := v1.memoryCost + v2.memoryCost
      dataCost := max v1.dataCost v2.dataCost
      successProb := v1.successProb + v2.successProb
      roundsCovered := v1.roundsCovered + v2.roundsCovered }
  | .rebound ir or_ c =>
    let child := c.eval env
    { timeCost := child.timeCost + or_
      memoryCost := child.memoryCost + ir
      dataCost := child.dataCost + or_
      successProb := child.successProb + or_
      roundsCovered := child.roundsCovered + ir + or_ }
  | .compose f s =>
    let vf := f.eval env; let vs := s.eval env
    { timeCost := vf.timeCost + vs.timeCost
      memoryCost := max vf.memoryCost vs.memoryCost
      dataCost := max vf.dataCost vs.dataCost
      successProb := vf.successProb + vs.successProb
      roundsCovered := vf.roundsCovered + vs.roundsCovered }
  | .parallel l r =>
    let vl := l.eval env; let vr := r.eval env
    { timeCost := min vl.timeCost vr.timeCost
      memoryCost := min vl.memoryCost vr.memoryCost
      dataCost := min vl.dataCost vr.dataCost
      successProb := min vl.successProb vr.successProb
      roundsCovered := max vl.roundsCovered vr.roundsCovered }
  | .iterate n b =>
    let body := b.eval env
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
  | .slideAttack period c =>
    let child := c.eval env
    { timeCost := child.timeCost + period
      memoryCost := child.memoryCost + period
      dataCost := child.dataCost + period
      successProb := child.successProb
      roundsCovered := child.roundsCovered }
  | .integralAttack dim c =>
    let child := c.eval env
    { timeCost := child.timeCost + dim
      memoryCost := child.memoryCost + dim
      dataCost := child.dataCost + dim
      successProb := child.successProb
      roundsCovered := child.roundsCovered + 1 }
  | .cubeAttack dim c =>
    let child := c.eval env
    { timeCost := child.timeCost + dim * dim
      memoryCost := child.memoryCost + dim
      dataCost := child.dataCost + dim
      successProb := child.successProb
      roundsCovered := child.roundsCovered + 1 }
  | .zeroSumPartition dim c =>
    let child := c.eval env
    { timeCost := child.timeCost + dim
      memoryCost := child.memoryCost + dim
      dataCost := child.dataCost + dim
      successProb := child.successProb
      roundsCovered := child.roundsCovered + 1 }
  | .invariantSubspace bs c =>
    let child := c.eval env
    { timeCost := child.timeCost + bs
      memoryCost := child.memoryCost
      dataCost := child.dataCost
      successProb := child.successProb + bs
      roundsCovered := child.roundsCovered }
  | .divisionProperty bs c =>
    let child := c.eval env
    { timeCost := child.timeCost + bs
      memoryCost := child.memoryCost + bs
      dataCost := child.dataCost
      successProb := child.successProb
      roundsCovered := child.roundsCovered + 1 }
  | .var id => env id

-- ============================================================
-- Section 3: Reconstruct AttackExpr from AttackOp + children
-- ============================================================

/-- Reconstruct an AttackExpr from an AttackOp node and its children's expressions. -/
def reconstructAttack (op : AttackOp) (children : List AttackExpr) : Option AttackExpr :=
  match op with
  | .diffChar p _ => match children with | [c] => some (.diffChar p c) | _ => none
  | .truncatedDiff ab _ => match children with | [c] => some (.truncatedDiff ab c) | _ => none
  | .boomerang _ _ => match children with | [c1, c2] => some (.boomerang c1 c2) | _ => none
  | .impossible r _ => match children with | [c] => some (.impossible r c) | _ => none
  | .linearTrail b _ => match children with | [c] => some (.linearTrail b c) | _ => none
  | .linearHull n _ => match children with | [c] => some (.linearHull n c) | _ => none
  | .algebraicRelation d _ => match children with | [c] => some (.algebraicRelation d c) | _ => none
  | .grobnerStep _ => match children with | [c] => some (.grobnerStep c) | _ => none
  | .meetInMiddle sr _ _ => match children with | [c1, c2] => some (.meetInMiddle sr c1 c2) | _ => none
  | .rebound ir or_ _ => match children with | [c] => some (.rebound ir or_ c) | _ => none
  | .compose _ _ => match children with | [f, s] => some (.compose f s) | _ => none
  | .parallel _ _ => match children with | [l, r] => some (.parallel l r) | _ => none
  | .iterate n _ => match children with | [b] => some (.iterate n b) | _ => none
  | .const v => match children with | [] => some (.const v) | _ => none
  | .slideAttack p _ => match children with | [c] => some (.slideAttack p c) | _ => none
  | .integralAttack d _ => match children with | [c] => some (.integralAttack d c) | _ => none
  | .cubeAttack d _ => match children with | [c] => some (.cubeAttack d c) | _ => none
  | .zeroSumPartition d _ => match children with | [c] => some (.zeroSumPartition d c) | _ => none
  | .invariantSubspace bs _ => match children with | [c] => some (.invariantSubspace bs c) | _ => none
  | .divisionProperty bs _ => match children with | [c] => some (.divisionProperty bs c) | _ => none

-- ============================================================
-- Section 4: Typeclass instances
-- ============================================================

instance : Extractable AttackOp AttackExpr where
  reconstruct := reconstructAttack

instance : EvalExpr AttackExpr AttackSemantics where
  evalExpr := AttackExpr.eval

-- ============================================================
-- Section 5: Smoke tests
-- ============================================================

#eval AttackExpr.eval (.diffChar 6 (.const 0)) (fun _ => default)
-- Expected: {time=12, mem=6, data=6, prob=6, rounds=1}

#eval AttackExpr.eval (.compose (.diffChar 6 (.const 0)) (.linearTrail 14 (.const 0))) (fun _ => default)
-- Expected: compose of diff + linear

#eval AttackExpr.eval (.boomerang (.diffChar 6 (.const 0)) (.diffChar 8 (.const 0))) (fun _ => default)
-- Expected: boomerang of two diffs

end SuperHash
