# Insights: SuperHash v4.5 — Evolutionary Co-Evolution (Red Team vs Blue Team)

**Fecha**: 2026-03-15
**Base**: v4.0.0 (110 jobs, 0 sorry, ~1,350 thms, LLM-ready)

## HALLAZGO PRINCIPAL: TrustHash YA TIENE el Red Team

TrustHash contiene un sistema de ataques composicionales COMPLETO:
- `Attacks/Composition/Types.lean`: **AttackOp** con 14 constructores
- `Attacks/Composition/Rules/`: **27 composition rules** (5 diff + 3 linear + 4 algebraic + 4 structural + 3 hybrid + 8 auxiliares)
- `Attacks/Composition/EGraph/Core.lean`: **E-graph de ataques** completo (453 LOC, 94 declaraciones)
- 7 familias de ataques con `Spec.lean` + `CostModel.lean` cada una

Esto cambia radicalmente el esfuerzo: en vez de diseñar desde cero, ADAPTAMOS.

## 1. Reuse Inventory

### 100% Reusable (zero changes — solo instantiar typeclasses)
| Component | LOC | Theorems | What it provides |
|-----------|-----|----------|-----------------|
| EGraph/Core.lean | 257 | 29 | EGraph, add, merge, find, rebuild |
| EGraph/CoreSpec.lean | 1,301 | 79 | WellFormed, PostMergeInvariant |
| EGraph/Consistency.lean | 1,272 | 49 | ConsistentValuation (45 theorems) |
| EGraph/UnionFind.lean | 1,099 | 44 | UnionFind, WellFormed |
| EGraph/EMatch.lean | 148 | 13 | Pattern, ematch, RewriteRule |
| Pipeline/Saturate.lean | 676 | 28 | saturateF, preservation theorems |
| Pipeline/Extract.lean | — | — | extractF, Extractable, ExtractableSound |
| Pipeline/Soundness.lean | — | — | optimizeF_soundness (parametric!) |
| Pipeline/EMatchSpec.lean | 1,017 | 25 | PatternSoundRule (parametric!) |
| Pipeline/ILP*.lean | ~1,200 | ~30 | ILP extraction (parametric!) |
| Rules/SoundRule.lean | — | — | SoundRewriteRule, EquivalenceRule |
| **Total** | **~4,800** | **~350** | **Entire E-graph + pipeline engine** |

### Needs Instantiation (~550 LOC new)
- `NodeOps AttackOp` instance (~80 LOC)
- `NodeSemantics AttackOp AttackSemantics` + 4 axiom proofs (~250 LOC)
- `Extractable AttackOp AttackExpr` + `EvalExpr` (~100 LOC)
- `ExtractableSound` bridge proof (~120 LOC)

### Needs New Code (~1,000-1,550 LOC)
- `AttackOp` inductive (14 constructors, ~40 LOC)
- `AttackSemantics` structure (5 fields, ~20 LOC)
- `evalAttackSem` (composition algebra, ~150 LOC)
- `AttackExpr` + eval (~100 LOC)
- `AttackMetrics` + `attackDominates` + theorems (~100 LOC)
- Attack PatternSoundRules (5-7 rules, ~200 LOC)
- HashSpec bridge theorems (~200 LOC)
- `pipeline_duel` theorem (~100 LOC)
- `DuelState` + `duelStep` + co-evolution loop (~200 LOC)
- Non-vacuity examples (~100 LOC)

## 2. TrustHash Attack Infrastructure (to adapt)

### AttackOp Constructors (14, from TrustHash/Attacks/Composition/Types.lean)
```
Differential:  diffChar, truncatedDiff, boomerang, impossible
Linear:        linearTrail, linearHull
Algebraic:     algebraicRelation, grobnerStep
Structural:    meetInMiddle, rebound
Composition:   compose, parallel, iterate, const
```

### AttackSemantics (5 fields)
```
timeCost      : Nat  -- log2 of time complexity
memoryCost    : Nat  -- log2 of memory
dataCost      : Nat  -- log2 of chosen/known texts
successProb   : Nat  -- -log2 of success probability
roundsCovered : Nat  -- rounds the attack covers
```

### Composition Algebra
| Operation | timeCost | memoryCost | dataCost | successProb | roundsCovered |
|-----------|----------|------------|----------|-------------|---------------|
| compose(a,b) | a+b | max(a,b) | max(a,b) | a+b | a+b |
| parallel(a,b) | min(a,b) | min(a,b) | min(a,b) | min(a,b) | max(a,b) |
| iterate(n,x) | n*x | x | x | n*x | n*x |

### 27 Composition Rules (from TrustHash)
- **Differential (5)**: boomerang decomposition, truncated composition, impossible extension, round reduction, boomerang→rectangle
- **Linear (3)**: hull aggregation, bias composition (Piling-Up), trail extension
- **Algebraic (4)**: degree composition, identity, zero, const fold
- **Structural (4)**: MITM shift, rebound compose, zero-sum extension, round iteration
- **Hybrid (3)**: alg-diff hybrid, alg-linear hybrid, diff-linear bridge
- **AlgExpr-level (8)**: branch collapse, trail fold, zero/one simplification, const fold (both families)

## 3. Library Theorems for Red Team

### DynamicTreeProg — THE critical library
| Theorem | Role |
|---------|------|
| `treeFold_inv` | BACKBONE: invariant induction for attack trees |
| `treeFold_lower_bound` | BELLMAN: DP gives genuine minimum attack cost |
| `treeFold_combined_lower_bound` | Multi-criteria (time+memory) Pareto optimization |
| **`treeFold_compatible`** | **RED-BLUE BRIDGE: attack and defense DPs compose correctly** |
| `treeFold_relational_inv` | DP correctness: table entries represent all sub-attacks |
| `opt_substructure` | Bellman at join nodes |
| `forget_preserves_bound` | Marginalization preserves attack bounds |
| `additiveCost_append` | Attack cost decomposes over chains |

### LeanHash — Security hierarchy + attack targeting
| Theorem | Role |
|---------|------|
| `security_monotone` | Lattice-based attack propagation |
| `dominates_trans` | Pareto pruning of dominated attacks |
| `joux_complexity_linear_in_k` | Joux composability: LINEAR cost for exponential collisions |
| `structural_degradation` | Formal gap: structural < ideal security |
| `hierarchy_strict` | Collisions are the cheapest attack target |
| `length_extension` | Sequential attack composition via hash extension |

### VerifiedExtraction — Optimality guarantees
| Theorem | Role |
|---------|------|
| `dp_optimal_of_validNTD` | DP extraction finds MINIMUM-COST attack |
| `extractILP_correct` | ILP-guided attack extraction is correct |
| `ValidNTD` | Structural validity certificate for attack decomposition |

## 4. Duel Theorem — Formal Architecture

### Three Formulations (strongest to weakest)

**A. Complexity-theoretic** (NEEDS AXIOM):
"Security level IS a lower bound on any attack cost" — requires assumption about ALL algorithms.

**B. Pipeline Duel** (PROVABLE with bridge hypotheses):
```lean
theorem pipeline_duel (spec : HashSpec)
    (h_blue_spec : ∀ d ∈ blue_output, fitness_of d = verdict.security)
    (h_red_spec : ∀ a ∈ red_output, a.timeCost >= verdict.security)
    (h_coverage : ∀ a ∈ red_output, a.roundsCovered >= spec.numRounds) :
    ∀ d ∈ blue_output, ∀ a ∈ red_output, fitness_of d <= a.timeCost
```
Proof: `calc fitness_of d = verdict.security ≤ a.timeCost`

**C. Definitional** (TRIVIALLY TRUE):
`computeFullVerdict` already computes `min(all_attack_costs)` — the duel is built into the definition.

### The REAL insight
The duel theorem is NOT a deep result. It's a **structural observation**: both teams compute bounds on the SAME quantity (adversary's work factor) from opposite directions. The E-graph engine is the shared infrastructure. The `computeFullVerdict` bridge connects both sides.

What IS deep: the attack COMPOSITION RULES. Proving that `boomerang = compose(truncDiff, truncDiff)` is a claim about differential cryptanalysis. Each rule encodes years of cryptographic research.

### Provability Classification
| Component | Status | Technique |
|-----------|--------|-----------|
| AttackSemantics composition | PROVABLE | Nat arithmetic (add/max/min assoc) |
| boomerang_decompose | PROVABLE | Struct field arithmetic |
| impossible_extend | PROVABLE | Nat arithmetic on roundsCovered |
| linear_aggregate | PROVABLE | min on parallel |
| attack_pipeline_soundness | PROVABLE | Instantiate parametric pipeline |
| pipeline_duel (with bridges) | PROVABLE | calc chain |
| duel_security_nondecreasing | PROVABLE | E-graph monotonicity |
| "security IS lower bound on cost" | NEEDS AXIOM | Complexity theory |
| "boomerang prob = p1*p2" | NEEDS AXIOM | Probability independence |
| "saturation is complete" | UNDECIDABLE | Term rewriting theory |

## 5. Implementation DAG

```
N1: AttackOp + AttackNodeOps            [FUNDACIONAL]  ~150 LOC
  ↓
N2: AttackSemantics + evalAttackSem     [FUNDACIONAL]  ~200 LOC
  ↓
N3: NodeSemantics AttackOp AttackSem    [CRITICO]      ~150 LOC
  ↓
N4: AttackExpr + EvalExpr + ExtSound    [CRITICO]      ~100 LOC
  ↓ ↘
N5: Attack PatternSoundRules (5-7)      [PARALELO]     ~200 LOC
N6: attack_pipeline_soundness           [CRITICO]      ~150 LOC
  ↓
N7: HashSpec bridge theorems            [CRITICO]      ~200 LOC
  ↓
N8: pipeline_duel theorem               [HOJA]         ~100 LOC
  ↓
N9: DuelState + co-evolution loop       [HOJA]         ~200 LOC
N10: Non-vacuity + Python orchestrator  [HOJA]         ~100 LOC
```

**Critical path**: N1→N2→N3→N4→N6→N7→N8 (~1,050 LOC)
**Total**: ~1,550 LOC new Lean + Python updates

## 6. Co-Evolution Loop Design

```
DuelState:
  blueState : DesignLoopState      -- Blue: design E-graph
  redGraph  : EGraph AttackOp      -- Red: attack E-graph
  redRules  : List (PatternSoundRule AttackOp AttackSemantics)
  redPareto : List (AttackExpr × AttackMetrics)
  spec      : HashSpec             -- Shared specification
  fuel      : Nat

One duel round:
  1. Blue: saturateF with design rules → extract Pareto
  2. Red: saturateF with attack rules → extract min-cost attack
  3. If red.bestAttack.timeCost < blue.bestDesign.security:
       → Blue receives "pressure" (LLM proposes defensive mutations)
  4. If red cannot break:
       → Design certified against known attacks
  5. Convergence: when gap closes or fuel exhausted
```

## 7. What to Formalize in LeanHash

### New module: `LeanHash/AttackComposition.lean`
Theorems about attack cost algebra:
1. `compose_timeCost_assoc`: (a+b)+c = a+(b+c) for composed attacks
2. `parallel_timeCost_comm`: min(a,b) = min(b,a)
3. `iterate_timeCost_mul`: n*(m*x) = (n*m)*x
4. `compose_rounds_additive`: rounds(compose(a,b)) = rounds(a) + rounds(b)
5. `parallel_rounds_max`: rounds(parallel(a,b)) = max(rounds(a), rounds(b))
6. `boomerang_cost_eq_compose`: boomerang(p1,p2).time = trunc(p1).time + trunc(p2).time
7. `attack_dominates_trans`: transitivity of attack Pareto dominance
8. `attack_dominates_irrefl`: irreflexivity
9. `optimal_attack_le_any`: min-cost attack ≤ any valid attack
10. `compose_monotone`: if a1 dominates a2, compose(a1,b) dominates compose(a2,b)

### New module: `LeanHash/DuelBounds.lean`
1. `duel_lower_bound`: security(d) ≥ min(attack_costs) by definition
2. `duel_monotone_blue`: blue security non-decreasing across iterations
3. `duel_monotone_red`: red attack cost non-increasing across iterations
4. `duel_gap_nonneg`: security - best_attack ≥ 0 (design is at least as secure as cheapest attack)
5. `convergence_implies_tight`: if gap = 0 then security = exact attack cost

## 8. Risk Assessment

| Phase | Risk | Mitigation |
|-------|------|-----------|
| AttackOp + NodeOps | LOW | Clone of CryptoOp pattern |
| AttackSemantics composition | LOW | Pure Nat arithmetic |
| NodeSemantics instance | MEDIUM | 4 axiom proofs (144 subgoals for skeleton) |
| Attack rules soundness | MEDIUM | Each rule is a simp proof |
| attack_pipeline_soundness | LOW | Instantiate parametric pipeline |
| HashSpec bridge | MEDIUM | Connecting fitness to verdict |
| pipeline_duel | LOW | calc chain |
| Co-evolution loop | LOW | Clone of designLoop with dual state |
| Python orchestrator | LOW | Extend design_loop.py |
| Cryptographic soundness axioms | NOT A RISK | Documented as axioms, not sorry |

## 9. Estimated Impact

| Metric | v4.0 | v4.5 target |
|--------|------|-------------|
| Build jobs | 110 | ~125 |
| LOC | ~27K | ~29K |
| Theorems | ~1,350 | ~1,500 |
| Sorry | 0 | 0 |
| E-graph instances | 1 (CryptoOp) | 2 (CryptoOp + AttackOp) |
| Pipeline instances | 1 (Blue) | 2 (Blue + Red) |
| Modes of operation | 1 (design) | 3 (design + audit + co-evolve) |
