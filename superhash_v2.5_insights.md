# Insights: SuperHash v2.5 — Closing the Crypto Semantics Gap

**Fecha**: 2026-03-13
**Dominio**: lean4
**Estado del objeto**: upgrade (v2.0 infrastructure complete, crypto semantics absent)
**Profundidad**: deep (3 agentes, 6 librerías auditadas, búsqueda online exhaustiva)

---

## 1. Análisis del Objeto de Estudio

### Resumen

SuperHash v2.0 tiene infraestructura E-graph verificada (245+ teoremas, 0 sorry en core) pero usa aritmética Nat como modelo semántico en lugar de propiedades criptográficas reales. Las 5 brechas a cerrar son: (1) modelo semántico criptográfico, (2) conexión con TrustHash como fitness, (3) reglas de reescritura con pruebas criptográficas, (4) loop LLM+RLVF funcional, (5) capa BitVec completa para S-boxes.

### Keywords (20)

algebraic degree, differential uniformity, S-box, DDT, LAT, MDS matrix, branch number, wide trail, active S-boxes, Boura-Canteaut bound, BitVec, bv_decide, GF(2^n), Poseidon, AES, equality saturation, lean-egg, LLM-guided rewriting, RLVF, CryptoSemantics

### Estado actual

- **Infraestructura**: 95% (E-graph, saturation, extraction, Pareto — all working)
- **Criptografía**: 5% (Nat arithmetic stub, no real crypto properties)
- **Brecha central**: `evalCryptoOp` computa `d * v + b` en lugar de propiedades criptográficas reales

### Hallazgo clave de la auditoría

**Ningún theorem prover (Lean, Coq, Isabelle) ha formalizado**: uniformidad diferencial de S-boxes, cotas de grado algebraico (Boura-Canteaut), propiedad MDS, branch number, ni la estrategia wide trail. SuperHash v2.5 sería **el primer proyecto** en formalizar estas propiedades en Lean 4.

---

## 2. Lecciones Aplicables

### Lecciones Reutilizables

| ID | Título | Categoría | Aplicación v2.5 |
|----|--------|-----------|-----------------|
| **L-513** | Compositional End-to-End Pipeline Proofs | Pipeline | Patrón para pipeline: security_rules_saturate → fitness_computation → policy_extraction (~30 líneas) |
| **L-458** | Concrete evalOp vs typeclass NodeSemantics | Semántica | CryptoOp es tipo concreto → usar evalCryptoOpSem concreto, NO typeclass polimórfico |
| **L-465** | NodeSemantics typeclass mismatch con Option | Anti-patrón | NO forzar instancia OptiSat. Mantener semántica Val standalone |
| **L-376** | Total pattern semantics via default fallback | Semántica | S-box eval retorna Val con Inhabited, NO Option. Elimina cadenas de Option |
| **L-550** | Soundness bug: 0^0=1 en Lean | Soundness | TODAS las reglas con exponentes necesitan guardia `exponent ≥ 1` |
| **L-523** | Large-scale library adaptation pattern | Adaptación | Copiar SuperHash v1.0 a v2.5: esperar ≤1 bug si Lean 4.28 fijo |
| **L-659** | Extension-only architecture non-recursive | LLM | Fitness function sin loops internos → precondición explícita NonRecursive |
| **L-617** | Pipeline #eval tests as specification oracle | Testing | 10+ `#eval` tests como oráculo antes de proof formal |

### Anti-Patrones

1. **Forzar OptiSat NodeSemantics en Option-returning semantics** (L-465) — type mismatch
2. **Patrones de exponente sin lower bound** (L-550) — 0^0=1 trap
3. **Option-returning eval en downstream theorems** (L-376) — cascading checks
4. **Identity passes `:= id` sin documentar** — fake completeness
5. **Adaptar código entre versiones Lean diferentes** (L-523) — 5x más bugs

### Técnicas Clave

| Técnica | Aplicación v2.5 |
|---------|-----------------|
| Compositional pipeline soundness (L-513) | Probar saturateF_soundness + computeF_soundness + extractF_soundness separados, componer |
| Concrete evalOp para dominio fijo (L-458) | evalCryptoOpSem sobre CryptoSemantics, no typeclass |
| Standalone Val-returning semantics (L-376) | S-box evaluation retorna Val ∈ CryptoSemantics con Inhabited |
| Non-vacuity via #eval oracle suite (L-617) | 10 fitness function tests antes de proof formal |

---

## 3. Bibliografía Existente Relevante

### Documentos Clave por Gap

#### Gap 1: S-box Differential Uniformity

| Documento | Carpeta | Relevancia |
|-----------|---------|-----------|
| **A review of cryptographic properties of S-boxes** (Dey, Ghosh) | criptografia/ | DDT, LAT, δ, NL, SAC, BIC para 4-bit y 8-bit. Definiciones matemáticas completas |
| **STP-based model for S-box design** (Lu et al.) | criptografia/ | Transforma propiedades S-box a problemas SMT — informa approach bv_decide |
| **Lightweight S-Boxes via Feistel/MISTY** (Canteaut et al., 2015) | criptografia/ | Lower bounds en δ para Feistel/MISTY structures. Formalizables |
| **Security of Poseidon** (Kovalchuk et al., 2021) | criptografia/ | Análisis diferencial/lineal sobre Fp, S-boxes activas, MDS branch numbers |
| **Trail-Estimator** (Peyrin et al., 2025) | hash-security/ | Verificación automática de trails diferenciales. Inspira verifier en Lean |

#### Gap 2: Algebraic Degree

| Documento | Carpeta | Relevancia |
|-----------|---------|-----------|
| **On the influence of algebraic degree of F^{-1}** (Boura-Canteaut, 2011) | hash-security/ | **EL paper fundacional**: `deg(G∘F) ≤ n - ceil((n-deg(G))/deg(F^{-1}))`. MUST-FORMALIZE |
| **Zero-Sum Distinguishers** (Boura-Canteaut, 2010) | hash-security/ | Conexión grado algebraico ↔ distinguishers. Walsh spectrum bounds |
| **STARK-friendly Hash Security Report v2** (Canteaut et al., 2020) | hash-security/ | Análisis de grado de GMiMC, Poseidon, Rescue. Argumento de round count |
| **AO Polynomial Decomposition** (Yang et al., 2025) | criptografia/ | Ataques por descomposición polinomial sobre F_{2^n} |

#### Gap 3: MDS / Branch Number

| Documento | Carpeta | Relevancia |
|-----------|---------|-----------|
| **Rescue-Prime Specification** (Szepieniec et al., 2020) | hash-security/ | Construcción MDS via Vandermonde sobre Fp. Definición formal MDS |
| **Security of Poseidon** (Kovalchuk et al., 2021) | criptografia/ | `BN(L) = min_{x≠0}(wt(x) + wt(L(x)))`. Conecta BN con S-boxes activas |
| **Poseidon** (Grassi et al., 2019) | criptografia/ | Argumento wide trail para determinar round count |

#### Gap 4: LLM + RLVF

| Documento | Carpeta | Relevancia |
|-----------|---------|-----------|
| **Equality Saturation Guided by LLMs** (Peng, 2025) | optimizacion/ | LGuess: LLM propone checkpoints, E-graph llena gaps. 255/320 vs 204/320 |
| **Guided Equality Saturation** (Koehler et al., POPL 2024) | optimizacion/ | Semi-automático con sketches humanos |

#### Gap 5: E-graph + Equality Saturation

| Documento | Carpeta | Relevancia |
|-----------|---------|-----------|
| **lean-egg** (Rossel, Goens, POPL 2026) | verificacion/ | Táctica de equality saturation para Lean 4. Rewrites condicionales |
| **egg** (Willsey et al., POPL 2021) | optimizacion/ | Fundación del motor E-graph |
| **SmoothE** (Cai et al., ASPLOS 2025) | optimizacion/ | Extracción diferenciable GPU-accelerated |
| **Ruler** (Nandi et al., OOPSLA 2021) | optimizacion/ | Descubrimiento automático de rewrite rules |

### Gaps Bibliográficos Críticos

| Gap | Descripción | Formalización existente? |
|-----|-------------|--------------------------|
| S-box differential uniformity formal | DDT computation + δ bound | **NO** — novel en cualquier prover |
| Boura-Canteaut algebraic degree bound | `deg(G∘F) ≤ n - ceil(...)` | **NO** — solo paper-and-pencil |
| MDS property formal proof | Todas las submatrices cuadradas no-singulares | **NO** — requiere álgebra lineal |
| Wide trail strategy formal | Counting argument BN → active S-boxes → security | **NO** — solo paper-and-pencil |
| bv_decide for S-box properties | SAT-based proof of δ for concrete S-boxes | **Parcial** — LNSym usa bv_decide para SHA/AES ops |

---

## 4. Estrategias y Decisiones Previas

### Estrategias Ganadoras de Librerías Internas

| Estrategia | Proyecto | Resultado | Aplicación v2.5 |
|-----------|---------|-----------|-----------------|
| Typeclass-parametrized E-graph | OptiSat | 499 thms, 0 sorry | NodeOps CryptoOp → NodeOps CryptoSemanticOp |
| Pattern.eval denotational semantics | OptiSat | Eliminó PreservesCV | CryptoExpr.eval sobre CryptoSemantics |
| Three-Tier Bridge (Shell/Core/Spec) | OptiSat v1.3 | Unified extraction | LLM en Shell, verified core, spec composition |
| Copy-not-import libraries | All projects | Zero coupling | Copiar teoremas de LeanHash, no depender |
| Fuel-bounded saturation | OptiSat/SuperHash | Terminación garantizada | Mantener para v2.5 |
| Mirror inductive para extraction | VerifiedExtraction | extractF_correct | CryptoExpr mirrors CryptoOp para extracción |
| Decidable certificate checking | VerifiedExtraction | extractILP_correct | Verificar soluciones ILP sin trust externo |

### Decisiones Arquitecturales Relevantes

| Decisión | Justificación | Impacto v2.5 |
|---------|--------------|-------------|
| Val := Nat (v1.0) | Métricas abstractas suficientes para pipeline | **CAMBIAR**: Val := CryptoSemantics para v2.5 |
| Sin Mathlib (v1.0) | Build <60s, zero coupling | **MANTENER**: BitVec es core, GF(2^n) si necesario via Mathlib |
| Dos niveles de reglas | Equivalence (=) vs Improvement (≥) | **EXTENDER**: Agregar ConditionalSecurityRule con precondiciones crypto |
| Pareto via scalarización | Solo convex hull (v1.0) | **UPGRADE**: SmoothE para non-convex (ya parcialmente en v2.0) |

### Benchmarks de Referencia

| Proyecto | Métrica | Valor | Contexto |
|----------|---------|-------|----------|
| LeanHash | Teoremas | ~160 | 15 archivos, 0 sorry, crypto properties |
| OptiSat | Teoremas | 499 | E-graph completo con pipeline soundness |
| VerifiedExtraction | Teoremas | 203 | Greedy + ILP extraction verified |
| SuperHash v1.0 | Teoremas | 323+ | Pipeline E2E, 0 sorry |
| SuperHash v2.0 | Build jobs | 41 | Infrastructure + stubs |

---

## 5. Nueva Bibliografía Encontrada (Online Research)

### Repositorios Clave Descubiertos

| Repo | URL | Descripción | Gaps |
|------|-----|-------------|------|
| **LNSym** (AWS) | github.com/leanprover/LNSym | ARM crypto verification. **bv_decide para SHA/AES**. Gold standard BitVec crypto | 1, 5 |
| **lean-egg** (Rossel) | github.com/marcusrossel/lean-egg | Equality saturation tactic para Lean 4. Rewrites condicionales. **POPL 2026** | 5 |
| **AMO-Lean** (LambdaClass) | github.com/lambdaclass/amo-lean | Lean 4 → eqsat → C/SIMD. Mathlib rewrites. FFT via equality saturation | 5 |
| **lean-crypto** (Hendrix) | github.com/joehendrix/lean-crypto | AES/SHA/SHAKE specs ejecutables en Lean 4. S-box tables concretas | 1 |
| **VCV-io** (Tumad) | github.com/dtumad/VCV-io | Crypto proofs computacionales en Lean 4. Oracle computations, Fiat-Shamir | 4 |
| **Fiat Crypto** (MIT) | github.com/mit-plv/fiat-crypto | Crypto aritmética verificada en Coq. En BoringSSL/Chrome | 3 |
| **hacspec** | hacspec.org | Rust subset → F*/EasyCrypt/Coq. Specs criptográficas | 1-4 |
| **Jasmin** | github.com/jasmin-lang/jasmin | Crypto implementations verificadas (Coq). ChaCha20, Poly1305 | 1 |

### Papers Online Relevantes

| Paper | Fuente | Relevancia |
|-------|--------|-----------|
| **Computationally-Sound Symbolic Crypto in Lean** (ePrint 2025/1700) | IACR | CSF 2026. Framework Lean 4 crypto proofs simbólicos → computacionales |
| **RLVF: Self-Proving Models** (arXiv 2405.15722) | arXiv | 40% → 79.3% verifiability. Metodología RLVF con binary verifier |
| **lean-egg POPL 2026** (Rossel, Goens) | POPL | Conditional rewrites en Lean via e-graphs. Puente directo para crypto rules |

---

## 6. Insights de Nueva Bibliografía

### Insight 1: LNSym demuestra bv_decide para crypto real en Lean 4

AWS usa `bv_decide` (CaDiCaL SAT + LRAT certificates) para verificar operaciones SHA y AES a nivel de bits ARM. Las pruebas son automáticas para BitVec ≤ 64 bits. Para S-boxes de 8 bits (AES), `bv_decide` puede verificar propiedades concretas como `∀ a b : BitVec 8, DDT(sbox, a, b) ≤ 4`.

**Impacto**: Gap 5 (BitVec) es solucionable con tooling existente. No requiere proofs manuales para propiedades concretas de S-boxes.

### Insight 2: lean-egg es el puente entre E-graphs y Lean proofs

Marcus Rossel (POPL 2026) implementó una táctica que traduce teoremas Lean a conditional rewrite rules para un backend egg (Rust). Esto permite: (1) descubrir equivalencias automáticamente, (2) verificar que las rewrite rules son sound via el kernel de Lean. **SuperHash podría usar lean-egg para verificar automáticamente reglas propuestas por LLM**.

**Impacto**: Gap 4 (LLM+RLVF) se simplifica si lean-egg verifica rules automáticamente en lugar de generar proofs custom.

### Insight 3: Ningún prover ha formalizado la criptografía estructural de hashes

La auditoría confirma: differential uniformity, algebraic degree bounds (Boura-Canteaut), MDS property, branch number, wide trail — NINGUNO está formalizado en ningún theorem prover. Los trabajos existentes (CryptoVerif, CryptHOL, VCV-io) formalizan seguridad game-based (IND-CPA, etc.), no propiedades estructurales de primitivas.

**Impacto**: SuperHash v2.5 sería genuinamente novel. Pero también significa que no hay referencia para copiar — todo es from scratch.

### Insight 4: AMO-Lean muestra el patrón arquitectónico correcto

LambdaClass's AMO-Lean: Lean 4 specs → equality saturation (via egg) → optimized code. Compila teoremas de Mathlib como rewrite rules. Genera Cooley-Tukey FFT via equality saturation. **Este es exactamente el patrón que SuperHash necesita**, pero aplicado a crypto design en lugar de arithmetic optimization.

### Insight 5: La cota de Boura-Canteaut es el teorema fundacional

`deg(G ∘ F) ≤ n - ⌈(n - deg(G)) / deg(F⁻¹)⌉`

Este single theorem es la base de TODOS los argumentos de grado algebraico en hash design. Poseidon, Rescue, GMiMC — todos usan esta cota para determinar round counts. Formalizarlo en Lean 4 sería **el teorema más impactante** de v2.5.

---

## 7. Síntesis de Insights

### Hallazgos Clave (Top 10)

1. **NINGÚN prover tiene crypto structural properties** — SuperHash v2.5 sería novel (y publicable)
2. **LeanHash tiene ~160 teoremas directamente reutilizables** — SboxProperties, MDSMatrix, DesignSpace son starting points
3. **bv_decide resuelve Gap 5** (BitVec) para S-boxes concretas ≤ 64 bits — LNSym lo demuestra
4. **lean-egg (POPL 2026) simplifica Gap 4** — verifica rewrite rules automáticamente via equality saturation
5. **Boura-Canteaut bound es EL teorema fundacional** — formalizar `deg(G∘F) ≤ n - ⌈(n-deg(G))/deg(F⁻¹)⌉`
6. **AMO-Lean es el patrón arquitectónico** — Lean specs → eqsat → optimized output
7. **VerifiedExtraction tiene extractF_correct y extractILP_correct** (0 sorry) — adoptar directamente
8. **L-458 + L-376: usar semántica Val concreta con Inhabited** — NO typeclass polimórfico, NO Option
9. **L-550: guardia 0^0=1 obligatoria** en toda regla con exponentes
10. **Gap 3 (MDS) requiere álgebra lineal** — posiblemente Mathlib para GaloisField, o abstracto sin Mathlib

### Riesgos

| Riesgo | Nivel | Mitigación |
|--------|-------|-----------|
| Boura-Canteaut bound es hard (ceil + division + inversion degree) | ALTO | Formalizar caso especial (deg=n-1) primero, generalizar después |
| MDS property requiere álgebra lineal sobre campos finitos | ALTO | Abstracto: `axiom mds_property` con non-vacuity via decide/native_decide para 4x4 |
| bv_decide timeout para S-boxes de 8+ bits con propiedades complejas | MEDIO | Usar `native_decide` como fallback, o factorizar por diferencia individual |
| lean-egg es WIP (no stable release) | MEDIO | Usar como inspiración, implementar mini-version si necesario |
| Formalización from scratch sin referencia en otro prover | MEDIO | Usar papers como spec, no código existente |

### Recomendaciones para Planificación

1. **Fase 1 (Fundacional)**: Formalizar CryptoSemantics structure + S-box properties concretas via bv_decide
2. **Fase 2 (Bridge)**: Conectar CryptoSemantics con evalCryptoOp via bridge theorems
3. **Fase 3 (Rules)**: Formalizar 3-5 reglas crypto reales con pruebas (sboxSubstitute, roundReduce, wideTrailImprove)
4. **Fase 4 (Integration)**: Conectar con TrustHash fitness + lean-egg para rule verification
5. **Fase 5 (Loop)**: LLM+RLVF funcional con fitness function real

### Recursos Prioritarios

1. **LeanHash/SboxProperties.lean** — copiar/adaptar 12 teoremas de propiedades S-box
2. **LeanHash/MDSMatrix.lean** — copiar/adaptar branchNumber + wide trail lemmas
3. **LeanHash/DesignSpace.lean** — referencia para CryptoSemantics structure
4. **lean-egg repo** (github.com/marcusrossel/lean-egg) — estudiar para rule verification
5. **LNSym repo** (github.com/leanprover/LNSym) — estudiar bv_decide patterns para crypto
6. **Boura-Canteaut 2011 paper** — source para algebraic degree bound formalization

---

## 8. Código Reutilizable de Librerías Internas

### Matriz de Reutilización Detallada

| Componente v2.5 | LeanHash | OptiSat | VerifiedExtraction | DynTreeProg |
|------------------|----------|---------|-------------------|-------------|
| CryptoSemantics structure | DesignSpace.lean (DesignParams, SecurityMetrics) | — | — | — |
| S-box properties | SboxProperties.lean (12 thms) | — | — | — |
| MDS / branch number | MDSMatrix.lean (8 thms) | — | — | — |
| Algebraic degree | DesignSpace.lean (degree_mono_rounds) | — | — | — |
| Pareto dominance | DesignSpace.lean (dominates + 3 thms) | — | — | — |
| E-graph core | — | Core.lean (NodeOps, EGraph) | Core.lean (NodeOps) | — |
| Extraction (greedy) | — | — | Greedy.lean (extractF_correct) | — |
| Extraction (ILP) | — | — | ILP.lean (extractILP_correct) | — |
| Cost computation | — | CompletenessSpec.lean | — | SubsetOpt.lean |
| Pipeline soundness | — | — (pattern reusable) | — | — |
| Birthday/GBP/Joux | BirthdayBound, GBP, Joux (.lean) | — | — | — |
| Merkle-Damgard | MerkleDamgard.lean | — | — | — |
| Threat model | ThreatLattice.lean | — | — | — |
| Tree decomposition | — | — | — | NiceTree.lean (treeFold) |
| DP bounds | — | — | — | DPBound.lean (6 thms) |

### Prioridad de Adaptación

**Directamente copiable** (v2.5 Phase 1):
- `LeanHash.SboxProperties` → SuperHash/Concrete/SboxProperties.lean
- `LeanHash.MDSMatrix` → SuperHash/Concrete/MDSProperties.lean
- `LeanHash.DesignSpace` → ya parcialmente en SuperHash/DesignParams.lean
- `VerifiedExtraction.Greedy.extractF_correct` → ya adaptado en SuperHash

**Adaptar** (v2.5 Phase 2-3):
- `LeanHash.DesignSpace.SoundRewriteRule` → agregar campos crypto (δ, deg, BN)
- `OptiSat.Core.NodeOps` → extender para CryptoSemanticOp
- `LeanHash.BirthdayBound/GBP/Joux` → fitness function genérica

**Inspiración** (v2.5 Phase 4-5):
- `AMO-Lean` architecture → verified crypto optimization pipeline
- `lean-egg` tactic → automated rule verification

---

## 9. Teoremas Formalizables Extraídos

### Por Grupo Temático

| Grupo | Cantidad | Dificultad | Source |
|-------|----------|-----------|--------|
| S-box DDT/LAT properties | 8 | easy-medium | Dey review, Canteaut 2015 |
| Algebraic degree bounds | 5 | medium-hard | Boura-Canteaut 2011, StarkWare report |
| MDS / branch number | 6 | medium | Rescue-Prime, Kovalchuk 2021 |
| Wide trail strategy | 4 | medium | Kovalchuk 2021, Poseidon paper |
| Security bound composition | 5 | easy-medium | LeanHash existing theorems |
| Total | **28** | — | — |

### Teoremas Clave a Formalizar (Top 10)

#### T1: DDT Computation (Fundamental)
```
def DDT (sbox : BitVec n → BitVec n) (a b : BitVec n) : Nat :=
  (Finset.univ.filter (fun x => sbox x ^^^ sbox (x ^^^ a) = b)).card
```
**Source**: Dey review, Def 2.1
**Difficulty**: easy (definition only)
**Dependencies**: BitVec, Finset

#### T2: Differential Uniformity
```
def diffUniformity (sbox : BitVec n → BitVec n) : Nat :=
  Finset.sup Finset.univ (fun a => Finset.sup Finset.univ (fun b => DDT sbox a b))
```
**Source**: Dey review, Def 2.2
**Difficulty**: easy (definition only, builds on T1)

#### T3: APN Optimality
```
theorem apn_min_uniformity : ∀ (sbox : BitVec n → BitVec n), diffUniformity sbox ≥ 2
```
**Source**: Dey review, Thm 2.1
**Difficulty**: medium (requires counting argument over DDT)

#### T4: Nonlinearity from Walsh Spectrum
```
def nonlinearity (f : BitVec n → BitVec 1) : Nat :=
  2^(n-1) - (Finset.sup Finset.univ (fun w => |walshCoeff f w|)) / 2
```
**Source**: Dey review, Def 2.5
**Difficulty**: medium (Walsh transform definition)

#### T5: Bent Function Bound
```
theorem bent_max_NL (hn : Even n) :
    nonlinearity f ≤ 2^(n-1) - 2^(n/2 - 1)
```
**Source**: Dey review, Thm 2.3
**Difficulty**: medium

#### T6: Boura-Canteaut Degree Bound (THE KEY THEOREM)
```
theorem degree_composition_bound (F G : BitVec n → BitVec n)
    (hF : algebraicDegree F = d_F) (hG : algebraicDegree G = d_G)
    (hFinv : algebraicDegree (F⁻¹) = d_Finv) :
    algebraicDegree (G ∘ F) ≤ n - Nat.ceil ((n - d_G) / d_Finv)
```
**Source**: Boura-Canteaut 2011, Theorem 1
**Difficulty**: hard (requires ANF representation + ceil arithmetic)
**Impact**: CRITICAL — foundation for all degree-based security arguments

#### T7: Branch Number Definition + MDS Property
```
def branchNumber (M : Matrix t t (ZMod p)) : Nat :=
  (Finset.univ.filter (fun x => x ≠ 0)).inf
    (fun x => hammingWeight x + hammingWeight (M.mulVec x))

theorem mds_optimal_branch (M : Matrix t t (ZMod p)) (h : IsMDS M) :
    branchNumber M = t + 1
```
**Source**: Rescue-Prime, Kovalchuk 2021
**Difficulty**: medium (requires matrix operations over finite fields)

#### T8: Wide Trail Active S-box Lower Bound
```
theorem wide_trail_bound (BN numRounds : Nat) (hBN : BN ≥ 2) :
    activeMinSboxes BN numRounds ≥ BN * (numRounds / 2)
```
**Source**: Kovalchuk 2021, Section 2.2
**Difficulty**: easy (already partially in LeanHash.MDSMatrix)

#### T9: Security Level from Active S-boxes + Differential Uniformity
```
theorem security_from_active_sboxes (δ activeSboxes : Nat) (hδ : δ ≥ 2) :
    diffSecurityBits δ activeSboxes = activeSboxes * Nat.log2 (2^n / δ)
```
**Source**: Wide trail strategy, standard textbook result
**Difficulty**: easy-medium

#### T10: Pipeline Fitness = min(generic_floor, structural_cost)
```
def securityLevel (generic structural : Nat) : Nat :=
  min generic structural

theorem fitness_monotone_structural (g : Nat) (s1 s2 : Nat) (h : s1 ≤ s2) :
    securityLevel g s1 ≤ securityLevel g s2
```
**Source**: TrustHash architecture
**Difficulty**: trivial

### Orden de Dependencias

```
T1 (DDT) → T2 (diffUniformity) → T3 (APN)
                                 → T9 (security from δ)
T4 (nonlinearity) → T5 (bent bound)
T6 (Boura-Canteaut) — standalone, hardest
T7 (branchNumber) → T8 (wide trail) → T9
T10 (fitness) — standalone, trivial
```

---

## 10. Librería Destino: LeanHash

### Archivos a Crear/Extender

| Archivo | Contenido | Teoremas |
|---------|-----------|----------|
| `LeanHash/DDT.lean` (nuevo) | DDT computation, diffUniformity, APN | T1, T2, T3 |
| `LeanHash/Nonlinearity.lean` (nuevo) | Walsh spectrum, nonlinearity, bent bound | T4, T5 |
| `LeanHash/AlgebraicDegree.lean` (nuevo) | ANF, algebraicDegree, Boura-Canteaut bound | T6 |
| `LeanHash/MDSMatrix.lean` (extender) | branchNumber formal, MDS property | T7 (extend existing) |
| `LeanHash/WideTrial.lean` (nuevo) | Active S-box bound, security from active sboxes | T8, T9 |
| `LeanHash/SecurityLevel.lean` (nuevo) | Fitness function: min(generic, structural) | T10 |

### Estado Actual de LeanHash

- **Path**: `~/Documents/claudio/leanhash/`
- **Archivos**: 15
- **Teoremas**: ~160
- **Build**: OK (Lean 4 sin Mathlib)
- **Uso**: Copiar/adaptar al proyecto SuperHash

### Recomendación

Formalizar T1-T2-T3 (DDT, diffUniformity, APN) primero — son definiciones + 1 theorem fácil. Luego T7-T8-T9 (branch number, wide trail, security). T6 (Boura-Canteaut) es el más difícil y se deja para último.

**Para v2.5**: copiar los teoremas formalizados de LeanHash a SuperHash/Concrete/ y usarlos como base del CryptoSemantics model.
