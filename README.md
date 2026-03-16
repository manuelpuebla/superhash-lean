# SuperHash v4.5

**Automatic design of cryptographic hash functions with formal guarantees: E-graphs + verified pipeline over CryptoSemantics + adversarial co-evolution + GF(2^4) field arithmetic.**

## What is SuperHash?

SuperHash formalizes in Lean 4 a framework for the automatic design of cryptographic hash functions. Unlike tools that only *analyze* hashes, SuperHash *synthesizes* optimal designs by exhaustively exploring the space of equivalent designs via equality saturation over E-graphs.

The system operates at five levels:
1. **E-graph engine** (v1.0): verified motor for saturation + extraction + Pareto
2. **CryptoSemantics** (v2.5): evaluation with real cryptographic metrics (8 fields: algebraic degree, differential uniformity, linear bias, branch number, active S-boxes, latency, gate count, circuit depth)
3. **Information-theoretic bounds** (v2.6): security bounds backed by the Leftover Hash Lemma (Tyagi-Watanabe 2023) and ZK side-information analysis
4. **Bidirectional exploration** (v3.0): 15+ rewrite rules (simplification + expansion + bridges) with bidirectional design space exploration
5. **CryptoSemantics pipeline** (v3.2): master theorem `pipeline_soundness_crypto` -- the full pipeline (saturation -> extraction -> Pareto) is **semantically correct** for all 8 cryptographic metrics simultaneously

## What it solves

Hash function design is a problem of algebraic equivalence + multi-objective optimization. SuperHash formalizes each transformation as a verified rewrite rule and uses E-graphs to exhaustively explore the design space. The fitness function combines three formal bounds:

```
security_level = min(birthdayFloor, lhlExtractorBound, algebraicSecurityBound)
```

Each component is backed by a theorem verified in Lean 4. The **master theorem** (`pipeline_soundness_crypto`) guarantees that every design extracted from the E-graph preserves all 8 cryptographic metrics of the original design.

## Project metrics

| Metric | Value |
|--------|-------|
| Build jobs | 125 |
| Lean files | 127 |
| LOC | ~24,500 |
| Theorems + examples | ~1,289 |
| Sorry | 0 |
| Custom axioms | 0 (only `propext` + `Quot.sound`) |
| Rewrite rules (Nat) | 15 (5 simplification + 10 expansion) |
| CryptoSemantics-proven rules | 7 (iterateOne, composeAssoc, 5x iterateCompose) |
| Papers studied | 24 (UHF folder: universal hashing + expander graphs) |
| Lean | 4.28.0, no Mathlib |

## Architecture

### Core Pipeline

```
Design (CryptoExpr) --> E-graph saturation (verified rules)
    --> Pareto extraction (multi-objective)
    --> TrustHash verdict (security evaluation)
    --> Fitness: min(birthday, differential, algebraic)
```

### The LLM + E-graph + Lean Architecture

The key insight: an LLM searching alone is creative but unsound (it can hallucinate rules that break security). An E-graph with verified rules is exhaustive but uncreative (it only explores designs reachable from known rules). The combination is strictly more powerful than either component alone.

```
+----------+   proposes rules   +------------+
|   LLM    | ------------------> |   Lean 4   |
| (creative|                    | (verifier) |
|  engine) | <------------------ |            |
+----------+   sound? yes/no    +------------+
      |                              |
      | verified rules only          |
      v                              |
+------------------+                 |
|  E-graph engine  |  cost function  |
|  (exhaustive     | <---------------+
|   explorer)      |
+--------+---------+
         | Pareto front
         v
+------------------+
|  Extraction      |--> verified optimal designs
|  (ILP/greedy)    |
+------------------+
```

- The LLM draws *new roads* on the map (proposes novel rewrite rules)
- Lean *verifies* each road is structurally sound (the kernel is the oracle)
- The E-graph *explores* every road exhaustively (equality saturation)
- TrustHash *evaluates* the fitness of each destination (security analysis)
- RLVF *trains* the LLM to draw better roads (reinforcement learning from verified feedback)

### Adversarial Co-evolution (Blue vs Red)

SuperHash implements adversarial co-evolution: the Blue Team designs hash functions while the Red Team evolves attacks to break them. Each round, Blue receives the Red Team's cheapest attack cost and designs a hash that resists it; Red receives the new hash and finds cheaper attacks. Both teams feed into a Pareto Front that drives RLVF reward back to the LLM.

The critical property -- **security never decreases across rounds** -- is a theorem, not just an empirical observation:

```lean
theorem duel_security_nondecreasing :
  forall (n : Nat), security (duel_round (n+1)) >= security (duel_round n)
```

A second key theorem guarantees verdict monotonicity:

```lean
theorem verdict_security_mono_rounds :
  forall (r1 r2 : Nat), r1 <= r2 ->
    verdict (round r1) <= verdict (round r2)
```

The Red Team engine models **20 distinct attack types** (differential, linear, algebraic, interpolation, higher-order differential, impossible differential, truncated differential, boomerang, rectangle, integral, meet-in-the-middle, rebound, algebraic-differential hybrid, slide, related-key, invariant subspace, division property, yoyo, subspace trail, quantum collision search), each formalized as a cost function. The Red Team E-graph composes these attacks, finding combinations no single attack type would discover.

### CryptoSemantics (8 fields)

| Field | Description |
|-------|-------------|
| `algebraicDegree` | Polynomial degree over GF(2^n) |
| `differentialUniformity` | delta: max entries in DDT |
| `linearBias` | epsilon: max bias in LAT |
| `branchNumber` | Branch number of the MDS layer |
| `activeMinSboxes` | Min active S-boxes in differential trail |
| `latency` | Cycles for hardware implementation |
| `gateCount` | Number of gates in circuit |
| `circuitDepth` | Critical path depth (captures parallelism) |

The function `evalCryptoSem` computes these properties compositionally: sequential composition multiplies degrees, iteration exponentiates them, XOR yields at most the maximum. The master theorem `pipeline_soundness_crypto` proves that all 8 metrics are preserved through the full SuperHash pipeline.

## Usage modes

### 1. Security analysis (TrustHash mode)
Given a hash specification (HashSpec), compute the security verdict:
```lean
#eval computeFullVerdict aesSpec
-- { security := 49, generic := 64, differential := 300, ... }
```

### 2. Design space exploration (SuperHash mode)
Start from a design, saturate with rewrite rules, extract Pareto front:
```lean
let result := superhash_v2 (.spnBlock 10 (.const 7) (.const 5)) (fuel := 3)
```

### 3. Adversarial co-evolution (Duel mode)
Run Blue (design) vs Red (attack) co-evolution:
```lean
let state := DuelState.init (.spnBlock 10 (.const 7) (.const 5)) 3 128
let final := duelLoop state
```

### 4. S-box certification
Verify cryptographic properties of any S-box:
```lean
#eval autoSboxPipeline presentSboxTable -- DDT + LAT + AlgDeg certificate
```

### 5. GF(2^4) algebraic verification
Verify S-box properties over finite fields:
```lean
#eval gf16Mul (7 : Fin 16, by omega) (gf16Inv (7 : Fin 16, by omega)) -- = 1 (field axiom)
```

## Formal guarantees

### v3.2: Pipeline soundness over CryptoSemantics (master theorem)
```
theorem pipeline_soundness_crypto :
  forall (rules : List (PatternSoundRule CryptoOp CryptoSemantics))
    (g : EGraph CryptoOp) (env : Nat -> CryptoSemantics)
    (v : EClassId -> CryptoSemantics)
    (hcv : ConsistentValuation g env v) ... ->
  -- Part 1: Semantic correctness over ALL 8 crypto metrics
  (exists v_sat, forall p in output,
    EvalExpr.evalExpr p.1 env = v_sat (root g_sat.unionFind rootId))
  -- Part 2: Pareto optimality
  /\ (forall p q in output, p != q -> not (dominates p.2 q.2))
  -- Part 3: Output size bound
  /\ output.length <= weights.length
```

This guarantees that **every hash design extracted** from the E-graph after saturation preserves the 8 fields of CryptoSemantics: algebraicDegree, differentialUniformity, linearBias, branchNumber, activeMinSboxes, latency, gateCount, circuitDepth.

### v1.0: Pipeline soundness (Nat)
```
theorem pipeline_soundness :
  -- (1) Semantic correctness: extracted designs evaluate to root value
  -- (2) Pareto optimality: no design dominates another
  -- (3) Output bound: output.length <= weights.length
```

### v2.5: CryptoSemantics evaluation
`evalCryptoOpCS` computes real cryptographic properties:
- `compose`: degree **multiplies**, delta = max, BN = min, gates **sum**
- `iterate(r)`: degree = safePow(deg, r), gates = r * gates
- `xor`: degree = max, delta = max (parallel operation)
- `spongeBlock`: delta isolated by capacity (`min(delta, 2^cap)`)

### v2.6: Information-theoretic bounds (Tyagi-Watanabe)
- **Source entropy**: `k = activeSboxes * (n - ilog2(delta))` -- proven = LHL bound
- **Extractor bound**: `extractableBits = k - 2*securityBits`
- **2-UHF constraint**: `delta * 2^l <= 2^n` -- decidable check via `native_decide`
- **ZK side-info loss**: `zkSecurity = baseSecurity - transcriptBits`

### v3.0: Bidirectional design exploration
15+ rewrite rules enable genuine design space exploration:
- **5 simplification** (Nat): iterateOne, parallelIdentity, composeAssoc, roundCompose, iterateCompose
- **7 CryptoSemantics-proven**: iterateOne_cs, composeAssoc_cs, 5x iterateCompose_cs(n,2) for n in {2,4,5,8,10}
- **8 bridge rules**: 4 forward (block -> primitive) + 4 reverse (primitive -> block)
- **2 roundSplit**: `iterate(10,x) -> compose(iterate(5,x), iterate(5,x))` (AES/Poseidon)

**Key finding**: `parallelIdentity` and `roundCompose` are UNSOUND for CryptoSemantics:
- `parallelIdentity`: `min(branchNumber, 0) = 0 != branchNumber`
- `roundCompose`: compose multiplies degrees, round adds them

### v3.1: Multi-property security model (24 UHF papers)
**SecurityProfile** with 4 dimensions (Rogaway-Shrimpton 2004):
- `collisionBits`: Coll -- find any x!=x' with h(x)=h(x')
- `preImageBits`: Pre -- given y, find x with h(x)=y
- `secondPreImageBits`: Sec -- given x, find x'!=x with h(x)=h(x')
- `targetCRBits`: eSec -- target collision resistance

**Proven implications**: `Coll -> Pre bound` (derivation via birthday), `Coll -> eSec bound`.

**UHF theory** (Carter-Wegman 1979 + extensions):
- Carter-Wegman H1 family: `collision * m <= p^2` for prime p >= m
- Short-output: `2 <= 2^b` for b-bit truncation (collision bound)
- Composition: `(e1 + e2) * s = e1 * s + e2 * s` (universality preserving)

**Expander graph bounds** (Charles-Goren-Lauter, Petit, Zhupa-Polak):
- LP compression: LP231 (50%), LP352 (55%), LP362 (63%) of birthday
- DBL: 2x security improvement over single-block
- ZesT: collision security >= groupOrderBits/2 (provable, non-malleable)
- Post-quantum: `quantumBits * 2 >= classicalBits` (Grover bound)
- Branch-spectral bridge: connects SPN wide-trail to graph expansion

### Concrete verifications
```
AES-128 fitness:           min(64, 150, 140) = 64 bits (birthday-bounded)
Poseidon-128 (8 rounds):   min(128, 1008, 54) = 54 bits (algebraic weakness!)
Poseidon in STARK (30-bit transcript): 54 - 30 = 24 bits (CRITICALLY WEAK)
Rescue-Prime in ZK (20-bit transcript): 18 - 20 = 0 bits (BROKEN)
PRESENT S-box delta:       4 (DDT computation verified by native_decide)
AES satisfies 2-UHF:       4 * 2^6 = 256 = 2^8  (for 6-bit output)
Saturation non-vacuity:    6->17 nodes with 3 rules (native_decide verified)
```

## Bibliography (24 papers)

SuperHash integrates results from 24 papers on universal hash functions, expander graphs, and cryptographic design, organized in 4 tiers of relevance:

### Tier 1: Directly formalized foundations
| Paper | Year | Contribution to SuperHash |
|-------|------|--------------------------|
| Carter & Wegman, *Universal Classes of Hash Functions* | 1979 | H1 family (mod-p) with collision bound `collisions * m <= p^2` |
| Rogaway & Shrimpton, *Hash-Function Basics* | 2004 | 7 security notions: Coll, Sec, aSec, eSec, Pre, aPre, ePre |
| Naor & Yung, *Universal One-Way Hash Functions* | 1991 | UOWHF: composition preserves target-collision resistance |
| *New Bounds for Almost Universal Hash Functions* | -- | Combinatorial lower bound for key length of epsilon-AU families |
| Nguyen & Roscoe, *Short-Output Universal Hash Functions* | 2011 | Collision prob = 2^(1-b) for b-bit output |

### Tier 2: New design paradigms
| Paper | Year | Contribution to SuperHash |
|-------|------|--------------------------|
| Charles, Goren & Lauter, *Hash Functions from Expander Graphs* | -- | Provable collision resistance from isogeny hardness |
| Rogaway & Steinberger, *Hash from Fixed-Key Blockciphers* | 2008 | LP family: LP231 (50%), LP352 (55%), LP362 (63%) of birthday bound |
| Hirose, *Double-Block-Length Hash Functions* | 2006 | DBL: 2x security improvement over single-block |
| Zhupa & Polak, *Keyed Hash from Large Girth Expander Graphs* | 2022 | Post-quantum: DMAC based on cycle-finding, ~4 ops/bit |

### Tier 3: Theoretical foundations
| Paper | Year | Contribution to SuperHash |
|-------|------|--------------------------|
| Tsurumaru & Hayashi, *Dual Universality* | 2012 | epsilon-almost dual universal2, connection to QKD |
| Caillat-Grenier, *Expander Graphs and IT Crypto* (thesis) | 2024 | Spectral gap <-> branch number bridge |
| Preneel, *The State of Cryptographic Hash Functions* | 1999 | Taxonomy of generic attacks (MITM, herding, fixed-point) |
| Al-Kuwari et al., *Recent Design Trends* | 2011 | Multi-Property Preservation (MPP), wide/double pipe |

### Tier 4: Context and anti-patterns
| Paper | Year | Contribution to SuperHash |
|-------|------|--------------------------|
| Tillich & Zemor, *Collisions for the LPS Hash* | 2007 | Anti-pattern: LPS has quasi-linear collisions |
| Petit, *On Graph-Based Cryptographic Hash Functions* (thesis) | 2009 | Atlas of attacks on expander hashes; ZesT = best variant |
| Petit, *On Expander Hash Functions* (thesis) | 2009 | ZesT: collision resistant + parallelizable + non-malleable |

## Stack and sources

- **Lean 4.28.0** without Mathlib
- **LeanHash** (~440 theorems, 0 sorry) -- S-box properties, MDS, Boura-Canteaut, universal hash families (Carter-Wegman, epsilon-AU, dual universality), expander graphs (LP, DBL, ZesT), security notions (Rogaway-Shrimpton)
- **TrustHash** (~3,546 declarations) -- pipeline patterns, sound hash rules, DP over tree decomposition
- **OptiSat** (~499 theorems) -- adapted E-graph infrastructure

## Project structure

```
SuperHash/
+-- CryptoOp.lean              -- 12 constructors (8 primitive + 4 block)
+-- DesignParams.lean           -- DesignParams, SecurityMetrics
+-- CryptoNodeOps.lean          -- NodeOps typeclass (12 constructors)
+-- EGraph/                     -- Verified E-graph engine
|   +-- Core.lean, CoreSpec.lean, UnionFind.lean
|   +-- Consistency.lean        -- ConsistentValuation (45 theorems)
|   +-- EMatch.lean, AddNodeTriple.lean, Tests.lean
+-- Rules/                      -- Verified rewrite rules
|   +-- SoundRule.lean          -- EquivalenceRule + ImprovementRule
|   +-- CryptoRules.lean        -- 10 concrete rules (Nat)
|   +-- CryptoRulesCS.lean      -- 7 CryptoSemantics rules (0 sorry)
|   +-- BlockBridge.lean        -- 4 bridges (spnBlock <-> iterate.compose)
|   +-- ExpansionRules.lean     -- 10 expansion rules (reverse bridges + roundSplit)
|   +-- NonVacuity.lean
+-- Pipeline/                   -- Saturation and extraction pipeline
|   +-- Saturate.lean, Extract.lean, Soundness.lean
|   +-- Integration.lean        -- superhash_pipeline
|   +-- MasterTheorem.lean      -- pipeline_soundness (Nat, 3-part)
|   +-- MasterTheoremCS.lean    -- pipeline_soundness_crypto (CryptoSemantics, 3-part)
+-- Crypto/                     -- Real cryptographic semantics
|   +-- Semantics.lean          -- CryptoSemantics (8 fields)
|   +-- CryptoEval.lean         -- evalCryptoSem, safePow
|   +-- CryptoNodeSemantics.lean -- NodeSemantics CryptoOp CryptoSemantics instance
|   +-- SecurityNotions.lean    -- SecurityProfile (Rogaway-Shrimpton) + UOWHF + MPP
|   +-- ExpanderBounds.lean     -- Expander + LP + DBL + ZesT + post-quantum
|   +-- UHFConstraint.lean      -- 2-UHF + Carter-Wegman H1 + epsilon-AU + short-output
|   +-- DDT.lean                -- DDT computation, CertifiedSbox (PRESENT delta=4)
|   +-- AESSbox.lean            -- Full 256-entry AES S-box (delta=4, native_decide)
|   +-- AlgebraicDegree.lean    -- ANF, ilog2 monotone, Boura-Canteaut concrete
|   +-- Fitness.lean            -- min(birthday, differential, algebraic)
|   +-- SourceEntropy.lean      -- DDT delta -> source entropy k (LHL)
|   +-- ExtractorBound.lean     -- extractableBits = k - 2s
|   +-- ZKSideInfo.lean         -- zkSecurity = base - transcript
|   +-- BouraCanteutBound.lean  -- 58 thms: BCD11, BC13, iterated bounds
|   +-- HigherOrderDiff.lean    -- 44 thms: derivative vanishing, zero-sum
|   +-- LinearLayerDegree.lean  -- 67 thms: SPN phase analysis, R_exp transition
+-- TrustHash/                  -- TrustHash-style verification
|   +-- NiceTree.lean           -- Nice tree decomposition + DP
|   +-- Verdict.lean            -- Security verdict (min of 5 metrics)
+-- Bridge/                     -- Inter-system bridges
|   +-- TrustHashFitness.lean   -- CryptoSemantics -> HashSpec bridge
+-- Pareto/                     -- Multi-objective extraction
+-- Discovery/                  -- RuleCandidate, RulePool (LLM integration)
+-- DesignLoop/                 -- Fuel-bounded autonomous loop
+-- Concrete/                   -- BitVec ops + bridge
+-- SmoothE/                    -- Non-linear cost model
+-- Instances/                  -- Concrete designs + demos
```

## Formal guarantees

## Version history

| Version | Content | Status |
|---------|---------|--------|
| v1.0 | E-graph engine + pipeline + master theorem | ✓ Complete |
| v2.0 | Block constructors + rule discovery + design loop | ✓ Complete |
| v2.5 | CryptoSemantics + DDT + algebraic degree + fitness | ✓ Complete |
| v2.6 | Information-theoretic bounds (LHL, 2-UHF, ZK side-info) | ✓ Complete |
| v2.7 | Zero sorry + AES DDT + NodeSemantics CryptoSemantics | ✓ Complete |
| v2.8 | Boura-Canteaut bounds (169 thms) + OptiSat completeness | ✓ Complete |
| v2.9 | Equality saturation ACTIVE + TrustHash DP verdict | ✓ Complete |
| v2.9.1 | Autopsy fixes (6 findings: 3 CRITICAL + 2 HIGH + 1 MEDIUM) | ✓ Complete |
| v3.0 | Bidirectional exploration: 3 CS-proven rules + 10 expansion rules | ✓ Complete |
| v3.1 | UHF integration: SecurityProfile + Carter-Wegman + expander bounds | ✓ Complete |
| v3.2 | **pipeline_soundness_crypto** + autopsy fixes (2C + 3H + 2M) | ✓ Complete |
| v3.3 | TrustHash S-box pipeline + quantum bounds + division property + 4D threat lattice + Pareto 6D | ✓ Complete |
| v3.3.1 | Autopsy fixes: formula reconciliation + honest naming + dead code removal + documentation | ✓ Complete |
| v4.0 | Graph infrastructure + TreewidthDP + ILP extraction + LLM-ready Python orchestrator | ✓ Complete |
| v4.5 | Evolutionary co-evolution (Red Team vs Blue Team duel framework) | ✓ Complete |
| v4.5.1 | Autopsy fixes: designSecurityLevel real, defense_eq_attack_bound non-rfl, DPMultiTable.wellformed | ✓ Complete |
| v4.5.2 | Definitive autopsy: verdict_security_mono_rounds, designLoop_master CV+PMI+BNI, cv_unique_acyclic | ✓ Complete |
| v4.5.3 | Final cleanup: AcyclicClassDAG instantiation, T1=0, documentation | ✓ Complete |
| v4.5.4 | 6 attack models (slide, integral, cube, zeroSum, invariantSubspace, divisionProperty) + S-box library + GF(2^4) + circuitDepth + substitution rules | ✓ Complete |
| v4.5.5 | Domain semantic fixes: compose delta product, activeMinSboxes decount, Poseidon delta docs, AES degree BCD11, bridge rename | ✓ Complete |
| v4.5.6 | Active S-boxes formula: BN*R/2 -> BN*R (matching LeanHash/TrustHash) | ✓ Complete |
| v4.5.7 | Composition consistency: linearBias product, iterate delta/epsilon safePow, documentation | ✓ Complete |
| v4.5.8 | Documentation rewrite: Spanish -> English, architecture section from article, usage modes | ✓ Complete |

## Future work

1. **OptiSat CryptoSemantics** -- Completed (`extractAuto_complete` proven)
2. **TrustHash fitness integration** -- Mostly completed (NiceTree + Verdict + Bridge integrated)
3. **General Boura-Canteaut bound** -- Open (169 concrete theorems; general proof via Reed-Muller covering radius pending). Would be the first formalization in any proof assistant.
4. **LLM end-to-end integration** -- Open (Lean infrastructure ready; Python orchestrator not connected)
5. **Post-quantum hash design** -- Planned (TrustHash v5.0 AG quantum bounds available for integration)

## References

- Tyagi & Watanabe, *Information-Theoretic Cryptography*, Cambridge 2023
- Willsey et al., *egg: Fast and Extensible Equality Saturation*, POPL 2021
- Boura & Canteaut, *On the influence of algebraic degree*, EUROCRYPT 2011
- Daemen & Rijmen, *The Design of Rijndael* (Wide Trail Strategy), 2002
- Carter & Wegman, *Universal Classes of Hash Functions*, JCSS 1979
- Rogaway & Shrimpton, *Cryptographic Hash-Function Basics*, 2004
- Naor & Yung, *Universal One-Way Hash Functions*, STOC 1989
- Charles, Goren & Lauter, *Hash Functions from Expander Graphs*
- Rogaway & Steinberger, *Hash from Fixed-Key Blockciphers*, 2008
- Petit, *On Graph-Based Cryptographic Hash Functions*, PhD Thesis 2009
- Zhupa & Polak, *Keyed Hash from Large Girth Expander Graphs*, 2022
- Nguyen & Roscoe, *Short-Output Universal Hash Functions*, 2011

---

*Source code:* [github.com/manuelpuebla/superhash-lean](https://github.com/manuelpuebla/superhash-lean)
*125 build jobs · ~1,289 theorems · 0 sorry · ILP extraction · TreewidthDP · LLM-ready · Lean 4.28.0*
