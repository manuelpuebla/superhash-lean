# SuperHash v3.3

**Diseño automático de funciones hash criptográficas con garantías formales: E-graphs + pipeline verificado sobre CryptoSemantics + S-box certification pipeline + modelo de seguridad multi-propiedad + Pareto 6D + grafos expansores + ataques cuánticos.**

## Qué es

SuperHash formaliza en Lean 4 un framework para el diseño automático de funciones hash criptográficas. A diferencia de herramientas que solo *analizan* hashes, SuperHash *sintetiza* diseños óptimos explorando exhaustivamente el espacio de diseños equivalentes mediante equality saturation sobre E-graphs.

El sistema opera en cinco niveles:
1. **E-graph engine** (v1.0): motor verificado de saturation + extraction + Pareto
2. **CryptoSemantics** (v2.5): evaluación con métricas criptográficas reales (7 campos: grado algebraico, δ, ε, branch number, S-boxes activas, latencia, gates)
3. **Information-theoretic bounds** (v2.6): cotas de seguridad respaldadas por el Leftover Hash Lemma (Tyagi-Watanabe 2023) y análisis de side-information ZK
4. **Bidirectional exploration** (v3.0): 15+ reglas de reescritura (simplificación + expansión + bridges) con exploración bidireccional del espacio de diseños
5. **CryptoSemantics pipeline** (v3.2): master theorem `pipeline_soundness_crypto` — el pipeline completo (saturación → extracción → Pareto) es **semánticamente correcto** para las 7 métricas criptográficas simultáneamente

## Qué resuelve

El diseño de funciones hash es un problema de equivalencia algebraica + optimización multi-objetivo. SuperHash formaliza cada transformación como una regla de reescritura verificada, y usa E-graphs para explorar exhaustivamente el espacio de diseños. La fitness function combina tres cotas formales:

```
security_level = min(birthdayFloor, lhlExtractorBound, algebraicSecurityBound)
```

Cada componente respaldado por un teorema verificado en Lean 4. El **master theorem** (`pipeline_soundness_crypto`) garantiza que todo diseño extraído del E-graph preserva las 7 métricas criptográficas del diseño original.

## Métricas del proyecto

| Métrica | Valor |
|---------|-------|
| Build jobs | 91 |
| Archivos Lean | 88 |
| LOC | ~23,600 |
| Teoremas + examples | ~1,100 |
| Sorry | 0 |
| Axiomas custom | 0 (solo `propext` + `Quot.sound`) |
| Rewrite rules (Nat) | 15 (5 simplification + 10 expansion) |
| CryptoSemantics-proven rules | 7 (iterateOne, composeAssoc, 5× iterateCompose) |
| Papers estudiados | 24 (carpeta UHF: hash universales + grafos expansores) |
| Lean | 4.28.0, sin Mathlib |

## Bibliografía formalizada (24 papers)

SuperHash integra resultados de 24 papers sobre funciones hash universales, grafos expansores y diseño criptográfico, organizados en 4 tiers de relevancia:

### Tier 1: Fundamentos directamente formalizados
| Paper | Año | Contribución a SuperHash |
|-------|-----|-------------------------|
| Carter & Wegman, *Universal Classes of Hash Functions* | 1979 | Familia H₁ (mod-p) con cota de colisión `collisions * m ≤ p²` |
| Rogaway & Shrimpton, *Hash-Function Basics* | 2004 | 7 nociones de seguridad: Coll, Sec, aSec, eSec, Pre, aPre, ePre |
| Naor & Yung, *Universal One-Way Hash Functions* | 1991 | UOWHF: composición preserva target-collision resistance |
| *New Bounds for Almost Universal Hash Functions* | — | Cota combinatoria inferior para key length de ε-AU families |
| Nguyen & Roscoe, *Short-Output Universal Hash Functions* | 2011 | Collision prob = 2^(1-b) para output de b bits |

### Tier 2: Nuevos paradigmas de diseño
| Paper | Año | Contribución a SuperHash |
|-------|-----|-------------------------|
| Charles, Goren & Lauter, *Hash Functions from Expander Graphs* | — | Collision resistance provable desde hardness de isogenías |
| Rogaway & Steinberger, *Hash from Fixed-Key Blockciphers* | 2008 | Familia LP: LP231 (50%), LP352 (55%), LP362 (63%) del birthday bound |
| Hirose, *Double-Block-Length Hash Functions* | 2006 | DBL: 2× mejora de seguridad sobre single-block |
| Zhupa & Polak, *Keyed Hash from Large Girth Expander Graphs* | 2022 | Post-quantum: DMAC basado en cycle-finding, ~4 ops/bit |

### Tier 3: Fundamentos teóricos
| Paper | Año | Contribución a SuperHash |
|-------|-----|-------------------------|
| Tsurumaru & Hayashi, *Dual Universality* | 2012 | ε-almost dual universal₂, conexión con QKD |
| Caillat-Grenier, *Expander Graphs and IT Crypto* (thesis) | 2024 | Spectral gap ↔ branch number bridge |
| Preneel, *The State of Cryptographic Hash Functions* | 1999 | Taxonomía de ataques genéricos (MITM, herding, fixed-point) |
| Al-Kuwari et al., *Recent Design Trends* | 2011 | Multi-Property Preservation (MPP), wide/double pipe |

### Tier 4: Contexto y anti-patterns
| Paper | Año | Contribución a SuperHash |
|-------|-----|-------------------------|
| Tillich & Zémor, *Collisions for the LPS Hash* | 2007 | Anti-pattern: LPS tiene colisiones quasi-lineales |
| Petit, *On Graph-Based Cryptographic Hash Functions* (thesis) | 2009 | Atlas de ataques a expander hashes; ZesT = mejor variante |
| Petit, *On Expander Hash Functions* (thesis) | 2009 | ZesT: collision resistant + parallelizable + non-malleable |

## Stack y fuentes

- **Lean 4.28.0** sin Mathlib
- **LeanHash** (~440 teoremas, 0 sorry) — propiedades S-box, MDS, Boura-Canteaut, familias hash universales (Carter-Wegman, ε-AU, dual universality), grafos expansores (LP, DBL, ZesT), nociones de seguridad (Rogaway-Shrimpton)
- **TrustHash** (~3,546 declaraciones) — patrones de pipeline, reglas hash sound, DP sobre tree decomposition
- **OptiSat** (~499 teoremas) — infraestructura E-graph adaptada

## Estructura

```
SuperHash/
├── CryptoOp.lean              -- 12 constructores (8 primitivos + 4 bloques)
├── DesignParams.lean           -- DesignParams, SecurityMetrics
├── CryptoNodeOps.lean          -- NodeOps typeclass (12 constructores)
├── EGraph/                     -- Motor E-graph verificado
│   ├── Core.lean, CoreSpec.lean, UnionFind.lean
│   ├── Consistency.lean        -- ConsistentValuation (45 theorems)
│   ├── EMatch.lean, AddNodeTriple.lean, Tests.lean
├── Rules/                      -- Reglas de reescritura verificadas
│   ├── SoundRule.lean          -- EquivalenceRule + ImprovementRule
│   ├── CryptoRules.lean        -- 10 reglas concretas (Nat)
│   ├── CryptoRulesCS.lean      -- 7 reglas CryptoSemantics (0 sorry)
│   ├── BlockBridge.lean        -- 4 bridges (spnBlock ↔ iterate∘compose)
│   ├── ExpansionRules.lean     -- 10 expansion rules (reverse bridges + roundSplit)
│   └── NonVacuity.lean
├── Pipeline/                   -- Pipeline de saturación y extracción
│   ├── Saturate.lean, Extract.lean, Soundness.lean
│   ├── Integration.lean        -- superhash_pipeline
│   ├── MasterTheorem.lean      -- pipeline_soundness (Nat, 3-part)
│   └── MasterTheoremCS.lean    -- pipeline_soundness_crypto (CryptoSemantics, 3-part)
├── Crypto/                     -- Semántica criptográfica real
│   ├── Semantics.lean          -- CryptoSemantics (7 campos)
│   ├── CryptoEval.lean         -- evalCryptoSem, safePow
│   ├── CryptoNodeSemantics.lean -- NodeSemantics CryptoOp CryptoSemantics instance
│   ├── SecurityNotions.lean    -- SecurityProfile (Rogaway-Shrimpton) + UOWHF + MPP
│   ├── ExpanderBounds.lean     -- Expander + LP + DBL + ZesT + post-quantum
│   ├── UHFConstraint.lean      -- 2-UHF + Carter-Wegman H₁ + ε-AU + short-output
│   ├── DDT.lean                -- DDT computation, CertifiedSbox (PRESENT δ=4)
│   ├── AESSbox.lean            -- Full 256-entry AES S-box (δ=4, native_decide)
│   ├── AlgebraicDegree.lean    -- ANF, ilog2 monotone, Boura-Canteaut concrete
│   ├── Fitness.lean            -- min(birthday, differential, algebraic)
│   ├── SourceEntropy.lean      -- DDT δ → source entropy k (LHL)
│   ├── ExtractorBound.lean     -- extractableBits = k - 2s
│   ├── ZKSideInfo.lean         -- zkSecurity = base - transcript
│   ├── BouraCanteutBound.lean  -- 58 thms: BCD11, BC13, iterated bounds
│   ├── HigherOrderDiff.lean    -- 44 thms: derivative vanishing, zero-sum
│   └── LinearLayerDegree.lean  -- 67 thms: SPN phase analysis, R_exp transition
├── TrustHash/                  -- TrustHash-style verification
│   ├── NiceTree.lean           -- Nice tree decomposition + DP
│   └── Verdict.lean            -- Security verdict (min of 5 metrics)
├── Bridge/                     -- Inter-system bridges
│   └── TrustHashFitness.lean   -- CryptoSemantics → HashSpec bridge
├── Pareto/                     -- Extracción multi-objetivo
├── Discovery/                  -- RuleCandidate, RulePool (LLM integration)
├── DesignLoop/                 -- Loop autónomo fuel-bounded
├── Concrete/                   -- BitVec ops + bridge
├── SmoothE/                    -- Non-linear cost model
└── Instances/                  -- Diseños concretos + demos
```

## Garantías formales

### v3.2: Pipeline soundness sobre CryptoSemantics (master theorem)
```
theorem pipeline_soundness_crypto :
  ∀ (rules : List (PatternSoundRule CryptoOp CryptoSemantics))
    (g : EGraph CryptoOp) (env : Nat → CryptoSemantics)
    (v : EClassId → CryptoSemantics)
    (hcv : ConsistentValuation g env v) ... →
  -- Part 1: Semantic correctness over ALL 7 crypto metrics
  (∃ v_sat, ∀ p ∈ output,
    EvalExpr.evalExpr p.1 env = v_sat (root g_sat.unionFind rootId))
  -- Part 2: Pareto optimality
  ∧ (∀ p q ∈ output, p ≠ q → ¬dominates p.2 q.2)
  -- Part 3: Output size bound
  ∧ output.length ≤ weights.length
```

Esto garantiza que **todo diseño hash extraído** del E-graph después de saturación preserva los 7 campos de CryptoSemantics: algebraicDegree, differentialUniformity, linearBias, branchNumber, activeMinSboxes, latency, gateCount.

### v1.0: Pipeline soundness (Nat)
```
theorem pipeline_soundness :
  -- (1) Semantic correctness: extracted designs evaluate to root value
  -- (2) Pareto optimality: no design dominates another
  -- (3) Output bound: output.length ≤ weights.length
```

### v2.5: CryptoSemantics evaluation
`evalCryptoOpCS` computa propiedades criptográficas reales:
- `compose`: degree **multiplica**, δ = max, BN = min, gates **suman**
- `iterate(r)`: degree = safePow(deg, r), gates = r × gates
- `xor`: degree = max, δ = max (operación paralela)
- `spongeBlock`: δ aislada por capacidad (`min(δ, 2^cap)`)

### v2.6: Information-theoretic bounds (Tyagi-Watanabe)
- **Source entropy**: `k = activeSboxes × (n - ilog2(δ))` — probado = LHL bound
- **Extractor bound**: `extractableBits = k - 2·securityBits`
- **2-UHF constraint**: `δ · 2^l ≤ 2^n` — decidable check por `native_decide`
- **ZK side-info loss**: `zkSecurity = baseSecurity - transcriptBits`

### v3.0: Bidirectional design exploration
15+ rewrite rules enable genuine design space exploration:
- **5 simplification** (Nat): iterateOne, parallelIdentity, composeAssoc, roundCompose, iterateCompose
- **7 CryptoSemantics-proven**: iterateOne_cs, composeAssoc_cs, 5× iterateCompose_cs(n,2) for n∈{2,4,5,8,10}
- **8 bridge rules**: 4 forward (block→primitive) + 4 reverse (primitive→block)
- **2 roundSplit**: `iterate(10,x) → compose(iterate(5,x), iterate(5,x))` (AES/Poseidon)

**Key finding**: `parallelIdentity` and `roundCompose` are UNSOUND for CryptoSemantics:
- `parallelIdentity`: `min(branchNumber, 0) = 0 ≠ branchNumber`
- `roundCompose`: compose multiplies degrees, round adds them

### v3.1: Multi-property security model (24 UHF papers)
**SecurityProfile** con 4 dimensiones (Rogaway-Shrimpton 2004):
- `collisionBits`: Coll — find any x≠x' with h(x)=h(x')
- `preImageBits`: Pre — given y, find x with h(x)=y
- `secondPreImageBits`: Sec — given x, find x'≠x with h(x)=h(x')
- `targetCRBits`: eSec — target collision resistance

**Proven implications**: `Coll → Pre bound` (derivation via birthday), `Coll → eSec bound`.

**UHF theory** (Carter-Wegman 1979 + extensions):
- Carter-Wegman H₁ family: `collision * m ≤ p²` for prime p ≥ m
- Short-output: `2 ≤ 2^b` for b-bit truncation (collision bound)
- Composition: `(ε₁ + ε₂) * s = ε₁ * s + ε₂ * s` (universality preserving)

**Expander graph bounds** (Charles-Goren-Lauter, Petit, Zhupa-Polak):
- LP compression: LP231 (50%), LP352 (55%), LP362 (63%) of birthday
- DBL: 2× security improvement over single-block
- ZesT: collision security ≥ groupOrderBits/2 (provable, non-malleable)
- Post-quantum: `quantumBits * 2 ≥ classicalBits` (Grover bound)
- Branch ↔ spectral bridge: connects SPN wide-trail to graph expansion

### Concrete verifications
```
AES-128 fitness:           min(64, 150, 140) = 64 bits (birthday-bounded)
Poseidon-128 (8 rounds):   min(128, 1008, 54) = 54 bits (algebraic weakness!)
Poseidon in STARK (30-bit transcript): 54 - 30 = 24 bits (CRITICALLY WEAK)
Rescue-Prime in ZK (20-bit transcript): 18 - 20 = 0 bits (BROKEN)
PRESENT S-box δ:           4 (DDT computation verified by native_decide)
AES satisfies 2-UHF:       4 · 2^6 = 256 = 2^8 ✓ (for 6-bit output)
Saturation non-vacuity:    6→17 nodes with 3 rules (native_decide verified)
```

## Versiones

| Versión | Contenido | Estado |
|---------|-----------|--------|
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

## Work in progress

**Próximos pasos (ordenados por prioridad):**

### 1. Completar integración OptiSat sobre CryptoSemantics
`CompletenessSpec.lean` already copied from OptiSat. Need `extractAuto_complete` for CryptoSemantics.

### 2. Integración con TrustHash como evaluador de fitness
TrustHash core (NiceTree + Verdict) already integrated. Remaining: full S-box pipeline (~31/34 files).

### 3. Formalización general del bound de Boura-Canteaut
169 theorems for concrete cases. Missing: general proof via Reed-Muller covering radius.
Would be the first formalization in any proof assistant.

### 4. LLM end-to-end integration
Connect Python orchestrator (AXLE, RLVF) with the verified Lean pipeline.

## Referencias

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

*Código fuente:* [github.com/manuelpuebla/superhash-lean](https://github.com/manuelpuebla/superhash-lean)
*91 build jobs · ~1,100 teoremas · 0 sorry · S-box pipeline · Pareto 6D · quantum bounds · Lean 4.28.0*
