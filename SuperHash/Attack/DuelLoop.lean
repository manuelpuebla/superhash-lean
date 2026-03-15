import SuperHash.Attack.AttackOp
import SuperHash.Attack.AttackRules
import SuperHash.Attack.AttackSemantics
import SuperHash.Attack.AttackMetrics
import SuperHash.DesignLoop.Core

/-!
# SuperHash.Attack.DuelLoop — Co-Evolution Duel Loop (Blue vs Red)

Dual version of DesignLoop.Core. Runs Blue Team (design optimization) and
Red Team (attack optimization) in alternating steps within a single
fuel-bounded loop.

## Architecture

- `DuelState`: joint state of both E-graphs (Blue + Red), shared fuel
- `duelStep`: one round of Blue saturation → Red saturation → update fronts
- `duelLoop`: recursive driver with fuel-bounded termination

## Termination (fuel-bounded, same technique as designLoop)

`duelStep` strictly decreases `fuel` when `fuel > 0`.
`duelLoop` recurses on `state.fuel` and terminates by WF on Nat.

## Design Decisions

- Blue uses `cryptoPatternRules ++ expansionRules` (same as DesignLoop.Core)
- Red uses `attackRewriteRules` (from AttackRules.lean)
- Red Pareto front is simplified to `List Nat` (timeCost values only)
  to avoid circular dependencies with the full AttackSemantics extraction
- Both sides share the fuel counter (alternating rounds)
-/

namespace SuperHash

-- ============================================================
-- Section 1: Duel state
-- ============================================================

/-- Joint state of the Blue Team (design) and Red Team (attack) co-evolution loop. -/
structure DuelState where
  /-- Blue team: design E-graph state -/
  bluePool : List (RewriteRule CryptoOp)
  blueGraph : EGraph CryptoOp
  blueParetoFront : List (CryptoExpr × SecurityMetrics)
  blueRootId : EClassId
  /-- Red team: attack E-graph state -/
  redPool : List (RewriteRule AttackOp)
  redGraph : EGraph AttackOp
  redParetoFront : List Nat  -- simplified: just timeCost values
  redRootId : EClassId
  /-- Shared -/
  fuel : Nat
  round : Nat := 0

-- ============================================================
-- Section 2: Initialization
-- ============================================================

/-- Build initial Red Team E-graph from a brute-force constant attack.
    The attack graph starts with a single `const` node representing
    the brute-force baseline cost (e.g., 128 for AES-128). -/
private def initRedGraph (bruteForceCost : Nat) : (EClassId × EGraph AttackOp) :=
  let g := EGraph.empty (Op := AttackOp)
  g.add ⟨.const bruteForceCost⟩

/-- Initialize a DuelState from a CryptoExpr design and fuel budget.

    Blue side: initialized exactly as in DesignLoopState.init.
    Red side: starts with a brute-force cost node and the standard attack rules. -/
def DuelState.init (design : CryptoExpr) (fuel : Nat)
    (bruteForceCost : Nat := 128) : DuelState :=
  -- Blue: reuse DesignLoopState.init logic
  let blueG := EGraph.empty (Op := CryptoOp)
  let (blueRoot, blueG) := designToEGraph design blueG
  let bluePareto := extractParetoV2 blueG standardCostSuite 20 blueRoot
  let blueRules : List (RewriteRule CryptoOp) :=
    cryptoPatternRules.map (·.rule) ++ expansionRules
  -- Red: start with brute-force baseline
  let (redRoot, redG) := initRedGraph bruteForceCost
  let redPareto := [bruteForceCost]
  { bluePool := blueRules
  , blueGraph := blueG
  , blueParetoFront := bluePareto
  , blueRootId := blueRoot
  , redPool := attackRewriteRules
  , redGraph := redG
  , redParetoFront := redPareto
  , redRootId := redRoot
  , fuel := fuel
  , round := 0
  }

-- ============================================================
-- Section 3: Duel step
-- ============================================================

/-- Extract minimum timeCost from an AttackOp E-graph.
    Walks all nodes in the Red E-graph classes and computes
    evalAttackSem for leaf nodes (const), returning the minimum timeCost.

    This is a simplified extraction: we only look at const nodes
    (base attacks) since full recursive extraction requires the
    full NodeSemantics instance (Phase 1). -/
private def extractRedTimeCosts (g : EGraph AttackOp) : List Nat :=
  -- Walk all classes and find const nodes
  let folder := fun (acc : List Nat) (_id : EClassId) (ec : EClass AttackOp) =>
    ec.nodes.foldl (fun acc2 node =>
      match node.op with
      | .const cost => cost :: acc2
      | _ =>
        -- For non-leaf nodes, use localCost as a proxy
        node.op.localCost :: acc2
    ) acc
  g.classes.fold folder []

/-- One step of the co-evolution duel loop.

    When fuel > 0:
    1. Blue: saturate design E-graph with Blue rules, re-extract Pareto
    2. Red: saturate attack E-graph with Red rules, extract best attacks
    3. Update both Pareto fronts (non-regression)
    4. Decrease fuel

    When fuel = 0: return unchanged. -/
def duelStep (state : DuelState) : DuelState :=
  match state.fuel with
  | 0 => state  -- no fuel: return unchanged
  | fuel + 1 =>
    -- === Blue Team: saturate + extract ===
    let blueSat := saturateF 10 5 3 state.blueGraph state.bluePool
    let newBluePareto := extractParetoV2 blueSat standardCostSuite 20 state.blueRootId
    let bestBluePareto := if newBluePareto.length ≥ state.blueParetoFront.length
                          then newBluePareto else state.blueParetoFront
    -- === Red Team: saturate + extract ===
    let redSat := saturateF 10 5 3 state.redGraph state.redPool
    let rawRedCosts := extractRedTimeCosts redSat
    -- Keep the better Red front (more attack options = more diverse)
    let bestRedPareto := if rawRedCosts.length ≥ state.redParetoFront.length
                         then rawRedCosts else state.redParetoFront
    -- === Update state ===
    { state with
      blueGraph := blueSat
      blueParetoFront := bestBluePareto
      redGraph := redSat
      redParetoFront := bestRedPareto
      fuel := fuel
      round := state.round + 1
    }

-- ============================================================
-- Section 4: Duel loop (recursive with termination proof)
-- ============================================================

/-- Run the co-evolution duel loop for all remaining fuel.
    Alternates Blue and Red team steps until fuel is exhausted. -/
def duelLoop (state : DuelState) : DuelState :=
  match h : state.fuel with
  | 0 => state
  | fuel + 1 =>
    let state' := duelStep state
    have : state'.fuel < state.fuel := by
      simp only [state', duelStep, h]; omega
    duelLoop state'
termination_by state.fuel

-- ============================================================
-- Section 5: Termination theorems
-- ============================================================

/-- Fuel decreases strictly on each duel step (when fuel > 0). -/
theorem duelStep_fuel_decreasing (state : DuelState) (hfuel : state.fuel > 0) :
    (duelStep state).fuel < state.fuel := by
  cases hf : state.fuel with
  | zero => omega
  | succ n => simp [duelStep, hf]

/-- After the duel loop completes, fuel is 0. -/
theorem duelLoop_fuel_zero (state : DuelState) :
    (duelLoop state).fuel = 0 := by
  unfold duelLoop
  split
  · next h => exact h
  · apply duelLoop_fuel_zero
termination_by state.fuel
decreasing_by
  simp_wf
  have h := duelStep_fuel_decreasing state (by omega)
  exact h

-- ============================================================
-- Section 6: Smoke tests
-- ============================================================

-- Smoke test: 3-round duel on a small SPN design.
-- Blue starts with a 10-round SPN; Red starts with brute-force 128.
#eval
  let state := DuelState.init (.spnBlock 10 (.const 7) (.const 5)) 3 128
  let final := duelLoop state
  s!"Duel rounds: {final.round}, Blue Pareto: {final.blueParetoFront.length}, Red attacks: {final.redParetoFront.length}, Fuel: {final.fuel}"

-- Smoke test: verify fuel reaches 0 after duel loop.
#eval
  let state := DuelState.init (.iterate 5 (.compose (.const 3) (.const 2))) 5 64
  let final := duelLoop state
  s!"Fuel after 5 rounds: {final.fuel}, Round counter: {final.round}"

end SuperHash
