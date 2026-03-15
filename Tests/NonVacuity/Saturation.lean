import SuperHash.DesignLoop.Core
import SuperHash.Rules.CryptoRules

/-!
# Tests.NonVacuity.Saturation — Equality saturation with REAL crypto rules

v2.9: First test demonstrating that equality saturation with verified
rewrite rules discovers alternative hash designs. This is the "turn the key"
moment — the E-graph is no longer identity (rules := []).

## Rules active
1. iterateOne: iterate(1, x) → x
2. parallelIdentity: parallel(x, const(0)) → x
3. composeAssoc: compose(compose(x,y),z) → compose(x,compose(y,z))
4. roundCompose: round(d,b,x) → compose(sbox(d,x), const(b))
5. iterateCompose: iterate(n, iterate(m, x)) → iterate(n*m, x)
-/

namespace SuperHash

-- ============================================================
-- Section 1: Verify rules are active in designLoopStep
-- ============================================================

-- The design loop now uses cryptoPatternRules (5 rules, not [])
#eval cryptoPatternRules.length  -- 5

-- ============================================================
-- Section 2: Saturation produces non-trivial results
-- ============================================================

-- A design with iterate(1, body) should be simplified to body
-- by the iterateOne rule
private def iterateOneDesign : CryptoExpr := .iterate 1 (.const 42)
private def iterateOneGraph :=
  let g := EGraph.empty (Op := CryptoOp)
  let (_, g) := designToEGraph iterateOneDesign g
  g

-- Run saturation with active rules
#eval
  let g := iterateOneGraph
  let rules := cryptoPatternRules.map (·.rule)
  let g_sat := saturateF 10 5 3 g rules
  let s := g_sat.stats
  s!"After saturation: {s.numClasses} classes, {s.numNodes} nodes (was 2 classes, 2 nodes)"

-- A round(7,5,x) design should be decomposed into compose(sbox(7,x), const(5))
-- by the roundCompose rule
private def roundDesign : CryptoExpr := .round 7 5 (.const 0)
private def roundGraph :=
  let g := EGraph.empty (Op := CryptoOp)
  let (_, g) := designToEGraph roundDesign g
  g

#eval
  let g := roundGraph
  let rules := cryptoPatternRules.map (·.rule)
  let g_sat := saturateF 10 5 3 g rules
  let s := g_sat.stats
  s!"Round decomposition: {s.numClasses} classes, {s.numNodes} nodes (was 2 classes, 2 nodes)"

-- ============================================================
-- Section 3: Full pipeline with active rules
-- ============================================================

-- Run the design loop with an AES-like design
#eval
  let state := DesignLoopState.init (.iterate 10 (.compose (.sbox 7 (.const 0)) (.linear 5 (.const 0)))) 3
  let final := designLoop state
  s!"Loop: {final.round} rounds, Pareto: {final.paretoFront.length} designs, Fuel: {final.fuel}"

-- ============================================================
-- Section 4: Non-vacuity — saturation changes the E-graph
-- ============================================================

/-- Non-vacuity: saturation with roundCompose rule STRICTLY INCREASES
    the E-graph — round(7,5,x) is decomposed into compose(sbox(7,x), const(5)),
    creating 3 new nodes (from 2 to 5).
    v2.9.1 Fix 4: strict inequality (was reflexive ≥). -/
example :
  let g := roundGraph
  let rules := cryptoPatternRules.map (·.rule)
  let g_sat := saturateF 10 5 3 g rules
  g_sat.stats.numNodes > g.stats.numNodes := by native_decide

/-- Non-vacuity: the design loop with active rules terminates with fuel 0. -/
example :
  let state := DesignLoopState.init (.const 1) 2
  (designLoop state).fuel = 0 := designLoop_fuel_zero _

-- ============================================================
-- Section 5: Multi-rule saturation on multi-node graph
-- ============================================================

/-! ### Non-vacuity: actual saturation with multiple rules on a non-trivial graph

This section tests that the pipeline genuinely works on a graph with >=3 nodes,
applying >=2 distinct rules (iterateOne + composeAssoc + roundCompose).

Design: compose(compose(round(7,5,const(0)), sbox(3,const(0))), iterate(1,const(0)))
- 7 nodes in the initial E-graph
- iterateOne fires: iterate(1,const(0)) → const(0)
- roundCompose fires: round(7,5,const(0)) → compose(sbox(7,const(0)), const(5))
- composeAssoc fires: compose(compose(a,b),c) → compose(a,compose(b,c))
All three rules discover new equivalent expressions, strictly growing the graph. -/

/-- A design with 7 nodes that exercises iterateOne, roundCompose, AND composeAssoc. -/
private def multiRuleDesign : CryptoExpr :=
  .compose (.compose (.round 7 5 (.const 0)) (.sbox 3 (.const 0))) (.iterate 1 (.const 0))

private def multiRuleGraph :=
  let g := EGraph.empty (Op := CryptoOp)
  let (_, g) := designToEGraph multiRuleDesign g
  g

-- Smoke test: verify initial graph size and saturation growth
#eval
  let g := multiRuleGraph
  let rules := cryptoPatternRules.map (·.rule)
  let g_sat := saturateF 10 5 5 g rules
  let s0 := g.stats
  let s1 := g_sat.stats
  s!"Multi-rule: {s0.numClasses}→{s1.numClasses} classes, {s0.numNodes}→{s1.numNodes} nodes"

/-- Non-vacuity: multi-rule saturation on a graph with >=3 nodes strictly grows
    the E-graph. This proves rules genuinely fire, not just pass through. -/
example :
  let g := multiRuleGraph
  let rules := cryptoPatternRules.map (·.rule)
  let g_sat := saturateF 10 5 5 g rules
  g_sat.stats.numNodes > g.stats.numNodes := by native_decide

/-- Non-vacuity: the initial graph has at least 3 e-classes (non-trivial input). -/
example : multiRuleGraph.stats.numClasses ≥ 3 := by native_decide

/-- Non-vacuity: saturation also grows the number of e-classes (rules add new
    equivalent representations, not just nodes within existing classes). -/
example :
  let g := multiRuleGraph
  let rules := cryptoPatternRules.map (·.rule)
  let g_sat := saturateF 10 5 5 g rules
  g_sat.stats.numClasses > g.stats.numClasses := by native_decide

end SuperHash
