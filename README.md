# SuperHash v2.6

**Diseño automático de funciones hash criptográficas con garantías formales: E-graphs + semántica criptográfica verificada + fundamentos information-theoretic.**

## Qué es

SuperHash formaliza en Lean 4 un framework para el diseño automático de funciones hash criptográficas. A diferencia de herramientas que solo *analizan* hashes, SuperHash *sintetiza* diseños óptimos explorando exhaustivamente el espacio de diseños equivalentes mediante equality saturation sobre E-graphs.

El sistema opera en tres niveles:
1. **E-graph engine** (v1.0): motor verificado de saturation + extraction + Pareto
2. **CryptoSemantics** (v2.5): evaluación con métricas criptográficas reales (grado algebraico, δ, branch number, S-boxes activas)
3. **Information-theoretic bounds** (v2.6): cotas de seguridad respaldadas por el Leftover Hash Lemma y análisis de side-information ZK

## Qué resuelve

El diseño de funciones hash es un problema de equivalencia algebraica + optimización multi-objetivo. SuperHash formaliza cada transformación como una regla de reescritura verificada, y usa E-graphs para explorar exhaustivamente el espacio de diseños. La fitness function combina tres cotas formales:

```
security_level = min(birthdayFloor, lhlExtractorBound, algebraicSecurityBound)
```

Cada componente respaldado por un teorema verificado en Lean 4.

## Métricas del proyecto

| Métrica | Valor |
|---------|-------|
| Build jobs | 51 |
| Archivos Lean | ~50 |
| LOC | ~13,500 |
| Teoremas + examples | ~490 |
| Sorry | 2 (v2.0 legacy, no en código crypto) |
| Axiomas custom | 0 (solo `propext` + `Quot.sound`) |
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
│   ├── CryptoRules.lean        -- 10 reglas concretas
│   ├── BlockBridge.lean        -- 4 bridges (spnBlock ↔ iterate∘compose)
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
│   └── ZKSideInfo.lean         -- zkSecurity = base - transcript
├── Pareto/                     -- Extracción multi-objetivo
├── Discovery/                  -- RuleCandidate, RulePool (LLM integration)
├── DesignLoop/                 -- Loop autónomo fuel-bounded
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

## Work in progress

**Próximos pasos (ordenados por prioridad):**

### 1. Cerrar 2 sorry restantes
**Qué hacer**: Probar dos lemas técnicos pendientes de v2.0.
- `MasterTheoremV2.lean:49` — `designLoop_preserves_pool`: componer `designLoopStep_preserves_pool` (ya probado, es `rfl`) inductivamente sobre el loop recursivo con `decreasing_by`.
- `SmoothE/Extract.lean:57` — `extractParetoV2_length_le`: probar que `List.filterMap` + dedup + filter produce lista ≤ input. Requiere un lema auxiliar `filterMap_length_le` (no está en Init, trivial por inducción sobre la lista).

**Dificultad**: BAJA. Son cierres mecánicos, no conceptuales. Ambos sorry tienen la estrategia de proof documentada en el comentario adyacente. ~30 min.

### 2. AES S-box DDT certificada
**Qué hacer**: Definir la tabla completa de 256 entradas del AES S-box como `ConcreteSbox 8`, computar `diffUniformity` sobre ella, y verificar δ=4 via `native_decide`. Actualmente solo PRESENT (4-bit, 16 entradas) está certificado.

**Dificultad**: BAJA. El código (`ddtEntry`, `diffUniformity`, `CertifiedSbox`) ya existe y funciona para PRESENT. Solo se necesita escribir la tabla literal (256 valores hex del AES S-box, disponible en cualquier referencia) y esperar que `native_decide` termine. El DDT de AES tiene 256×256 = 65,536 comparaciones — debería correr en <10 segundos.

**Obstáculo potencial**: Si `native_decide` es demasiado lento para 8-bit (65K comparaciones), se puede factorizar la verificación en 256 lemas parciales (uno por fila del DDT) o usar `decide` con heartbeats aumentados.

### 3. Pipeline `pipeline_soundness` sobre `CryptoSemantics`
**Qué hacer**: El master theorem actual (`pipeline_soundness`) opera sobre `Val := Nat`. Crear una versión que opere sobre `CryptoSemantics` (7 campos: algebraicDegree, differentialUniformity, linearBias, branchNumber, activeMinSboxes, latency, gateCount). Esto requiere adaptar 5 componentes en cadena:
1. `instance : NodeSemantics CryptoOp CryptoSemantics` — instanciar el typeclass con `evalCryptoSem`
2. `ConsistentCryptoValuation` — adaptar la definición y los ~45 teoremas de preservación (merge, add, rebuild)
3. `saturateF_preserves_crypto_consistent` — propagar a través de la saturación
4. `extractF_crypto_correct` — extracción preserva semántica crypto
5. `pipeline_soundness_crypto` — componer todo en el master theorem

**Dificultad**: ALTA (por volumen, no por dificultad conceptual). Los ~200 theorems del E-graph core (Consistency.lean, CoreSpec.lean) están parametrizados por `[NodeSemantics Op Val]`, así que en principio basta instanciar el typeclass. El obstáculo real es que `evalCryptoSem` tiene cases para 12 constructores (vs 8 en v1.0), y cada prueba de preservación necesita cubrir los 4 nuevos cases (spnBlock, feistelBlock, spongeBlock, arxBlock). Estimación: 1-2 días.

**Obstáculo principal**: Los proofs de `processClass_shi_combined` (120 líneas) y `merge_consistent` (96 líneas) hacen `cases op` internamente. Agregar 4 constructores multiplica las subgoals. Puede requerir refactorizar esos proofs para usar `<;>` combinators más agresivamente.

### 4. Completar integración OptiSat sobre CryptoSemantics
**Qué hacer**: OptiSat (499 theorems, 0 sorry, `~/Documents/claudio/optisat/`) ya provee el motor E-graph que SuperHash usa. La integración pendiente consiste en:
1. Verificar que `NodeOps CryptoOp` (ya instanciado con 12 constructores) es compatible con la versión OptiSat
2. Instanciar `NodeSemantics CryptoOp CryptoSemantics` (mismo que item 3 arriba — son el mismo trabajo)
3. Copiar/adaptar los theorems de `CompletenessSpec.lean` de OptiSat (BestNodeInv, acyclicity, cost computation) para CryptoSemantics
4. Adaptar `extractAuto_complete` (OptiSat) para demostrar que la extracción greedy sobre CryptoSemantics es óptima

**Dificultad**: MEDIA-ALTA. OptiSat está en Lean 4 puro (misma base que SuperHash), pero usa una versión anterior del toolchain. Los tipos son compatibles conceptualmente pero pueden diferir en nombres de API (e.g., `Std.HashMap` vs `HashMap` en versiones diferentes de Lean).

**Por qué OptiSat en vez de lean-egg**: OptiSat es infraestructura propia (499 theorems verificados, 0 sorry, sin dependencias externas). lean-egg (Marcus Rossel, POPL 2026) requiere un backend Rust (Cargo) y no tiene release estable. Usar OptiSat elimina la dependencia externa y mantiene toda la TCB dentro de Lean.

### 5. Integración con TrustHash como evaluador de fitness
**Qué hacer**: Usar el pipeline completo de TrustHash (3,546 declaraciones, `~/Documents/claudio/TrustHash/`) como función de fitness real en el loop autónomo. TrustHash provee:
- `AutoSboxPipeline`: S-box table → DDT/LAT/ANF → SboxCertifiedParams
- `RealSaturate`: E-graph saturation con 12 rewrite rules sound
- Constraint graph → tree decomposition → nice tree
- `SecurityDP`: DP multi-ronda sobre nice trees → cota de seguridad
- Veredicto: `security_level = min(generic_floor, structural_cost)`

**Dificultad**: ALTA. TrustHash usa Lean 4.16.0, SuperHash usa 4.28.0. No se puede importar directamente como dependencia lake — hay que copiar/adaptar. Las diferencias de API entre versiones (e.g., `Array.foldl` signature, `Std.HashMap` API, `omega` tactic availability) requieren ajustes en ~50 archivos adaptados. Estimación: 3-5 días.

**Obstáculo principal**: TrustHash define `HashOp` (12 operaciones hash) y `HashExprF` (expression forest) que son tipos DISTINTOS de `CryptoOp` y `CryptoExpr`. Se necesita un bridge type-level: o bien (a) unificar ambos tipos en uno solo, o bien (b) crear funciones de traducción `CryptoOp ↔ HashOp` con proofs de preservación. La opción (b) es más modular pero duplica definiciones.

### 6. Formalización del bound de Boura-Canteaut
**Qué hacer**: Probar el tight degree composition bound: `deg(G∘F) ≤ n - ⌈(n-deg(G))/deg(F⁻¹)⌉`. Este es EL resultado fundacional para determinar cuántas rondas necesita un hash (Poseidon, Rescue, GMiMC todos usan esta cota para sus round counts).

**Estado actual**: Tenemos verificación concreta para AES (`bouraCanteutBound_aes_concrete`: la fórmula da 7 vs naive 49, probado por `native_decide`) y la cota trivial (`degree_sub_le_n`: n-x ≤ n). Falta la prueba GENERAL de que la fórmula es un upper bound para `deg(G∘F)`.

**Dificultad**: MUY_ALTA. La prueba original (Boura & Canteaut, EUROCRYPT 2011, Theorem 1) usa el covering radius de códigos Reed-Muller punctured. Formalizar esto requiere:
1. Definir el código Reed-Muller RM(r, n) sobre GF(2)
2. Probar propiedades del covering radius (teorema de Delsarte)
3. Conectar covering radius con grado algebraico de composiciones
4. Ningún proof assistant (Lean, Coq, Isabelle) tiene Reed-Muller codes formalizados

**Estrategia alternativa**: Probar el caso especial para S-boxes bijectivas con `deg(F⁻¹) = n-1` (cubre AES, PRESENT). Este caso se reduce a: `deg(G∘F) ≤ n - 1` cuando `deg(G) < n` y F es permutación, que es más accesible (no requiere Reed-Muller, solo propiedades de permutaciones sobre GF(2)^n).

**Genuinamente novel**: Sería la primera formalización de este bound en cualquier proof assistant. Publicable como resultado independiente.

## Referencias

- Tyagi & Watanabe, *Information-Theoretic Cryptography*, Cambridge 2023
- Willsey et al., *egg: Fast and Extensible Equality Saturation*, POPL 2021
- Boura & Canteaut, *On the influence of algebraic degree*, EUROCRYPT 2011
- Daemen & Rijmen, *The Design of Rijndael* (Wide Trail Strategy), 2002

---

*Código fuente:* [github.com/manuelpuebla/superhash-lean](https://github.com/manuelpuebla/superhash-lean)
*51 build jobs · ~490 teoremas · Lean 4.28.0*
