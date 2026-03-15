# SuperHash v3.1

**Diseño automático de funciones hash criptográficas con garantías formales: E-graphs + semántica criptográfica verificada + exploración bidireccional + fundamentos information-theoretic + modelo de seguridad multi-propiedad (Rogaway-Shrimpton).**

## Qué es

SuperHash formaliza en Lean 4 un framework para el diseño automático de funciones hash criptográficas. A diferencia de herramientas que solo *analizan* hashes, SuperHash *sintetiza* diseños óptimos explorando exhaustivamente el espacio de diseños equivalentes mediante equality saturation sobre E-graphs.

El sistema opera en cuatro niveles:
1. **E-graph engine** (v1.0): motor verificado de saturation + extraction + Pareto
2. **CryptoSemantics** (v2.5): evaluación con métricas criptográficas reales (grado algebraico, δ, branch number, S-boxes activas)
3. **Information-theoretic bounds** (v2.6): cotas de seguridad respaldadas por el Leftover Hash Lemma y análisis de side-information ZK
4. **Bidirectional exploration** (v3.0): 15 reglas de reescritura (simplificación + expansión + bridges) con exploración bidireccional del espacio de diseños

## Qué resuelve

El diseño de funciones hash es un problema de equivalencia algebraica + optimización multi-objetivo. SuperHash formaliza cada transformación como una regla de reescritura verificada, y usa E-graphs para explorar exhaustivamente el espacio de diseños. La fitness function combina tres cotas formales:

```
security_level = min(birthdayFloor, lhlExtractorBound, algebraicSecurityBound)
```

Cada componente respaldado por un teorema verificado en Lean 4.

## Métricas del proyecto

| Métrica | Valor |
|---------|-------|
| Build jobs | 64 |
| Archivos Lean | 66 |
| LOC | ~18,500 |
| Teoremas + examples | ~800 |
| Sorry | 0 |
| Axiomas custom | 0 (solo `propext` + `Quot.sound`) |
| Rewrite rules | 15 (5 simplification + 10 expansion) |
| CryptoSemantics-proven rules | 3 (iterateOne, composeAssoc, iterateCompose) |
| Scripts Python | 6 |
| Lean | 4.28.0, sin Mathlib |

## Stack y fuentes

- **Lean 4.28.0** sin Mathlib
- **TrustHash** (~3,546 declaraciones) — patrones de pipeline, reglas hash sound, DP sobre tree decomposition
- **LeanHash** (~175 teoremas) — propiedades S-box, MDS, diseño hash, familias hash universales
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
│   ├── CryptoRulesCS.lean      -- 3 reglas CryptoSemantics (0 sorry)
│   ├── BlockBridge.lean        -- 4 bridges (spnBlock ↔ iterate∘compose)
│   ├── ExpansionRules.lean     -- 10 expansion rules (reverse bridges + roundSplit)
│   └── NonVacuity.lean
├── Pipeline/                   -- Pipeline de saturación y extracción
│   ├── Saturate.lean, Extract.lean, Soundness.lean
│   ├── Integration.lean        -- superhash_pipeline
│   └── MasterTheorem.lean      -- pipeline_soundness (3-part)
├── Crypto/                     -- v2.5+v2.6: Semántica criptográfica real
│   ├── Semantics.lean          -- CryptoSemantics (7 campos), SboxParams, MDS
│   ├── CryptoEval.lean         -- evalCryptoSem (reemplaza evalCryptoOp Nat)
│   ├── CryptoRule.lean         -- 5 reglas con precondiciones crypto
│   ├── DDT.lean                -- DDT computation, CertifiedSbox (PRESENT δ=4)
│   ├── AlgebraicDegree.lean    -- ANF, ilog2 monotone, Boura-Canteaut concrete
│   ├── Fitness.lean            -- min(birthday, differential, algebraic)
│   ├── SourceEntropy.lean      -- DDT δ → source entropy k (LHL)
│   ├── ExtractorBound.lean     -- extractableBits = k - 2s
│   ├── UHFConstraint.lean      -- 2-UHF: δ·2^l ≤ 2^n (decidable)
│   ├── ZKSideInfo.lean         -- zkSecurity = base - transcript
│   ├── AESSbox.lean            -- Full 256-entry AES S-box (δ=4, native_decide)
│   ├── CryptoNodeSemantics.lean -- NodeSemantics CryptoOp CryptoSemantics instance
│   ├── SecurityNotions.lean    -- v3.1: Rogaway-Shrimpton + UOWHF + MPP + bridges
│   ├── ExpanderBounds.lean     -- v3.1: Expander + LP + DBL + ZesT + post-quantum
│   ├── BouraCanteutBound.lean  -- 58 thms: BCD11, BC13, iterated bounds
│   ├── HigherOrderDiff.lean    -- 44 thms: derivative vanishing, zero-sum
│   └── LinearLayerDegree.lean  -- 67 thms: SPN phase analysis, R_exp transition
├── Pareto/                     -- Extracción multi-objetivo
├── Discovery/                  -- RuleCandidate, RulePool (LLM integration)
├── DesignLoop/                 -- Loop autónomo fuel-bounded
├── TrustHash/                  -- TrustHash-style verification
│   ├── NiceTree.lean           -- Nice tree decomposition + DP
│   └── Verdict.lean            -- Security verdict (min of 5 metrics)
├── Bridge/                     -- Inter-system bridges
│   └── TrustHashFitness.lean   -- CryptoSemantics → HashSpec bridge
├── Concrete/                   -- BitVec ops + bridge
├── SmoothE/                    -- Non-linear cost model
└── Instances/                  -- Diseños concretos + demos
scripts/                        -- Python: AXLE, RLVF, rule proposer, design loop
```

## Garantías formales

### v1.0: Pipeline soundness (master theorem)
```
theorem pipeline_soundness :
  -- (1) Semantic correctness: extracted designs evaluate to root value
  -- (2) Pareto optimality: no design dominates another
  -- (3) Output bound: output.length ≤ weights.length
```

### v2.5: CryptoSemantics evaluation
`evalCryptoSem` computa propiedades criptográficas reales:
- `compose`: degree **multiplica** (no suma)
- `iterate(r)`: degree = deg^r (exponenciación, no multiplicación)
- `xor`: degree = max (operación paralela, no aditiva)
- `spongeBlock`: δ aislada por capacidad (`min(δ, 2^cap)`)

### v2.6: Information-theoretic bounds (Tyagi-Watanabe)
- **Source entropy**: `k = activeSboxes × (n - ilog2(δ))` — probado = LHL bound
- **Extractor bound**: `extractableBits = k - 2·securityBits`
- **2-UHF constraint**: `δ · 2^l ≤ 2^n` — decidable check por `native_decide`
- **ZK side-info loss**: `zkSecurity = baseSecurity - transcriptBits`

### v3.0: Bidirectional design exploration
15 rewrite rules enable genuine design space exploration:
- **5 simplification** (Nat): iterateOne, parallelIdentity, composeAssoc, roundCompose, iterateCompose
- **3 CryptoSemantics-proven**: iterateOne_cs, composeAssoc_cs (`Nat.mul_assoc + max_assoc + min_assoc + add_assoc`), iterateCompose_cs (`safePow_safePow`)
- **8 bridge rules**: 4 forward (block→primitive) + 4 reverse (primitive→block)
- **2 roundSplit**: `iterate(10,x) → compose(iterate(5,x), iterate(5,x))` (AES/Poseidon)

**Key finding**: `parallelIdentity` and `roundCompose` are UNSOUND for CryptoSemantics:
- `parallelIdentity`: `min(branchNumber, 0) = 0 ≠ branchNumber`
- `roundCompose`: compose multiplies degrees, round adds them

### v3.1: Multi-property security model (24 UHF papers)
**SecurityProfile** with 4 dimensions (Rogaway-Shrimpton 2004):
- `collisionBits`: Coll — find any x≠x' with h(x)=h(x')
- `preImageBits`: Pre — given y, find x with h(x)=y
- `secondPreImageBits`: Sec — given x, find x'≠x with h(x)=h(x')
- `targetCRBits`: eSec — target collision resistance

**Proven implications**: `Coll → Sec`, `Coll → eSec`, `Pre ⊥ Coll` (independent).

**UHF theory** (Carter-Wegman 1979 + extensions):
- Carter-Wegman H₁ family: `collision * m ≤ p²` for prime p ≥ m
- ε-AU key length bound: `keyBits * (rangeSize - 1) ≥ (domainSize - 1) * epsilon`
- Short-output: `collision_prob ≤ 2/2^b` for b-bit truncation
- Composition: `ε₁ + ε₂` bound for composed families

**Expander graph bounds** (Charles-Goren-Lauter, Petit, Zhupa-Polak):
- Mixing lemma: `deviation² ≤ λ₂² · |S| · |T|`
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
| v3.0 | Bidirectional exploration: 3 CS-proven rules + 10 expansion rules + active saturation | ✓ Complete |
| v3.1 | UHF integration: SecurityProfile + Carter-Wegman + ε-AU + expander bounds + LP/DBL + post-quantum | ✓ Complete |

## Work in progress

**Próximos pasos (ordenados por prioridad):**

### 1. Pipeline `pipeline_soundness_crypto` sobre CryptoSemantics
**Qué hacer**: El master theorem actual opera sobre `Val := Nat`. El `NodeSemantics CryptoOp CryptoSemantics` instance ya existe (v2.7). La infraestructura es parametric — `optimizeF_soundness` and `saturateF_preserves_consistent_internal` are polymorphic. Only `superhash_pipeline_correct` is hardcoded to Nat. Need to create the crypto instantiation.

**Dificultad**: MEDIA. The parametric infrastructure means most proofs propagate automatically.

### 2. Completar integración OptiSat sobre CryptoSemantics
**Qué hacer**: `CompletenessSpec.lean` already copied from OptiSat. Need to adapt `extractAuto_complete` for CryptoSemantics extraction optimality.

**Dificultad**: MEDIA.

### 3. Integración con TrustHash como evaluador de fitness
**Qué hacer**: TrustHash core (NiceTree + Verdict) already integrated. Remaining: full S-box pipeline adaptation (~31/34 files).

**Dificultad**: ALTA. TrustHash uses Lean 4.16.0 vs 4.28.0.

### 4. Formalización general del bound de Boura-Canteaut
**Estado actual**: 169 theorems (BCD11, BC13, iterated bounds) for concrete cases (AES, Keccak, Poseidon). Missing: general proof via Reed-Muller covering radius.

**Dificultad**: MUY_ALTA. Would be the first formalization in any proof assistant.

### 5. LLM end-to-end integration
**Qué hacer**: Connect Python orchestrator (AXLE, RLVF) with the verified Lean pipeline for genuine AI-guided hash design.

## Referencias

- Tyagi & Watanabe, *Information-Theoretic Cryptography*, Cambridge 2023
- Willsey et al., *egg: Fast and Extensible Equality Saturation*, POPL 2021
- Boura & Canteaut, *On the influence of algebraic degree*, EUROCRYPT 2011
- Daemen & Rijmen, *The Design of Rijndael* (Wide Trail Strategy), 2002

---

*Código fuente:* [github.com/manuelpuebla/superhash-lean](https://github.com/manuelpuebla/superhash-lean)
*64 build jobs · ~800 teoremas · 0 sorry · 15 rewrite rules · Lean 4.28.0*
