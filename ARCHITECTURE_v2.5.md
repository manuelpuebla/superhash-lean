# SuperHash v2.5 — ARCHITECTURE

**Proyecto**: SuperHash v2.5
**Dominio**: Lean 4 (sin Mathlib) + adaptaciones de TrustHash/LeanHash
**Toolchain**: leanprover/lean4:v4.28.0
**Versión**: v2.5-planning
**Última actualización**: 2026-03-13
**Base**: v2.0 complete (41 build jobs, E-graph infrastructure, Val:=Nat stub)
**Objetivo**: Primera formalización de propiedades criptográficas estructurales (DDT, grado algebraico, wide trail) en cualquier theorem prover

---

## Visión

SuperHash v2.5 cierra la brecha semántica entre la infraestructura E-graph verificada (v2.0) y la criptografía real. Reemplaza `Val := Nat` con `CryptoSemantics` — un dominio que captura grado algebraico, uniformidad diferencial, branch number, S-boxes activas, y sesgo lineal. Las reglas de reescritura pasan de ser identidades del semianillo a transformaciones con pruebas de seguridad criptográfica.

**Fuentes de código reutilizable**:
- **LeanHash** (~160 theorems, `~/Documents/claudio/leanhash/`): Foundations — SboxProperties, MDSMatrix, DesignSpace, SPNDegree
- **TrustHash** (~3546 declarations, `~/Documents/claudio/TrustHash/`): Infrastructure — HashSoundRules, RealSaturate, AutoSboxPipeline, TreewidthDP

---

## Decisiones Arquitecturales (v2.5)

### D14: CryptoSemantics como dominio semántico
**Justificación**: Val:=Nat no distingue XOR de compose (ambos = suma). CryptoSemantics captura 6 métricas reales.
```lean
structure CryptoSemantics where
  algebraicDegree : Nat          -- deg del polinomio sobre GF(2^n)
  differentialUniformity : Nat   -- δ: max_{a,b} #{x : S(x)⊕S(x⊕a)=b}
  linearBias : Nat               -- ε: max sesgo LAT (QA #4: añadido)
  branchNumber : Nat             -- min peso diff de MDS matrix
  activeMinSboxes : Nat          -- min S-boxes activas en trail diferencial
  latency : Nat                  -- ciclos (modelo de performance)
  gateCount : Nat                -- gates (modelo de área)
```

### D15: Composición distingue sequential vs parallel (QA #1 — BLOCKING fix)
**Justificación**: Sequential composition: `deg(G∘F) ≤ deg(G)*deg(F)`, `δ` domain-specific. Parallel: `deg = max`, `δ = max`. Son operaciones criptográficamente distintas.
- `compose` (sequential): `deg *= child.deg`, `δ` via bound theorem
- `parallel`: `deg = max(l.deg, r.deg)`, `δ = max(l.δ, r.δ)`
- `iterate(r, f)`: `deg = f.deg^r` (upper bound), `activeSboxes = r * f.activeSboxes`

### D16: DDT via native_decide, no bv_decide (QA #2)
**Justificación**: `bv_decide` over `∀ x y : BitVec 8` genera 2^16 constraints — intractable. TrustHash usa `native_decide` con lookup tables pre-computadas. Patrón probado en AutoSboxPipeline.

### D17: CryptoSoundRule incluye dominates (QA #3)
**Justificación**: Reglas de mejora (SboxSubstitute, RoundReduce) son direccionales. La soundness requiere `dominates new_metrics old_metrics`. Copiar `dominates` de LeanHash/DesignSpace.lean.

### D18: Boura-Canteaut requiere IsPermutation (QA #6)
**Justificación**: El bound `deg(G∘F) ≤ n - ⌈(n-deg(G))/deg(F⁻¹)⌉` requiere que F sea biyección sobre GF(2)^n. AES S-box es permutación (well-known pero necesita proof formal).

### D19: Fitness function basada en bounds formales (QA #5)
**Justificación**: `algebraicDegree^treewidth` es heurístico. Fitness usa composición de bounds formalizados en LeanHash:
```
securityLevel = min(birthdayFloor, degreeSecurity, differentialBound)
```
Cada componente respaldado por un theorem.

### D20: v2.0 backward compatibility vía NatBridge (QA #10)
**Justificación**: v2.0 tiene 41 build jobs con Val:=Nat. NatBridge proyecta CryptoSemantics → Nat vía `algebraicDegree`. Tests v2.0 siguen pasando durante la transición.

---

## Fases del Proyecto

### Fase 1: Crypto Foundations (Copiar de LeanHash)
Copia y adapta ~55 teoremas de LeanHash como base criptográfica. Incluye propiedades S-box, MDS/branch number, security definitions, y SPN degree.

### Fase 2: S-box Certification + BitVec (Adaptar de TrustHash)
Formaliza DDT computation via native_decide, adapta SboxCertifiedParams y AutoSboxPipeline de TrustHash para certificación concreta de S-boxes.

### Fase 3: CryptoSemantics — The Core Gap
Reemplaza Val:=Nat con CryptoSemantics. Nueva evaluación semántica, NodeSemantics instance, ConsistentValuation adaptado, y bridge de backward compatibility.

### Fase 4: Crypto Rewrite Rules (Proofs Reales)
Reglas de reescritura con pruebas criptográficas: SboxSubstitute (δ constraints), RoundReduce (security bounds), WideTrailImprove (BN improvement), plus reglas adaptadas de TrustHash.

### Fase 5: Algebraic Degree — Crown Jewel
Formaliza ANF, algebraic degree, y el bound de Boura-Canteaut. Primera formalización en cualquier theorem prover. Incluye IsPermutation (D18).

### Fase 6: Pipeline Integration + Fitness
Compone todo en un pipeline con fitness function formal. Master theorem v2.5: E2E soundness con CryptoSemantics.

---

## DAG de Dependencias

```
FASE 1 (Foundations — copy LeanHash)
N1.1 ──→ N1.2 ──→ N1.3 ──→ N1.5
                   N1.4 ───→ N1.5

FASE 2 (S-box Cert — adapt TrustHash)       FASE 5 (Algebraic Degree)
N2.1 ──→ N2.2 ──→ N2.3 ──→ N2.4             N5.1 ──→ N5.2 ──→ N5.3 ──→ N5.4 ──→ N5.5
  ↑                                            ↑
N1.1 ──────────────────────────────────── N1.4─┘

FASE 3 (CryptoSemantics — THE CORE)
N3.1 ──→ N3.2 ──→ N3.3 ──→ N3.5 ──→ N3.6
               └──→ N3.4 ──┘
  ↑                   ↑
N1.3,N2.2 ──→ N3.1   N5.4 ──→ N3.6 (integra degree)

FASE 4 (Crypto Rules)
N4.1 ──→ N4.2 ──┐
     ──→ N4.3 ──┤
     ──→ N4.4 ──┼──→ N4.7
     ──→ N4.5 ──┤
     ──→ N4.6 ──┘
  ↑
N3.3 (rules need CryptoSemantics)

FASE 6 (Pipeline + Fitness)
N6.1 ──→ N6.2 ──→ N6.3 ──→ N6.4 ──→ N6.5 ──→ N6.6
  ↑         ↑         ↑
N1.3    N4.7,N3.5  N5.4 (degree integration)

Cross-phase:
  N1.1 → {N2.1, N5.1}
  N1.3,N2.2 → N3.1
  N3.3 → N4.1
  N5.4 → N3.6 (degree into semantics)
  N4.7,N3.5,N5.4 → N6.2
```

---

## Nodos Detallados

### Fase 1: Crypto Foundations (Copy LeanHash)

#### N1.1 — SboxParams + Properties [FUNDACIONAL]
- **Archivos**: `SuperHash/Crypto/SboxProperties.lean` (nuevo)
- **Deps**: ninguna
- **Source**: Copiar `LeanHash/SboxProperties.lean` (12 theorems) + adaptar tipos
- **Entregables**:
  - `structure SboxParams` (inputBits, diffUniformity, nonlinearity, algebraicDeg)
  - 12 theorems: `diff_uniformity_ceiling`, `bent_max_nonlinearity`, `apn_is_optimal_uniformity`, `degree_upper_bound`, `degree_lower_bound_bijective`, `xor_preserves_*`
  - Adapt types: LeanHash Nat fields → SuperHash convention
- **Dificultad**: BAJA (copy + type adapt)

#### N1.2 — MDS + Branch Number [FUNDACIONAL]
- **Archivos**: `SuperHash/Crypto/MDSProperties.lean` (nuevo)
- **Deps**: N1.1
- **Source**: Copiar `LeanHash/MDSMatrix.lean` (9 theorems)
- **Entregables**:
  - `def branchNumber`, `mds_branch_exceeds_dim`, `branch_number_positive`
  - `branch_number_active_sbox`, `wide_trail_lower_bound`, `more_rounds_more_active`
  - Poseidon MDS instances: `mds_poseidon_t3`, `mds_poseidon_t9`
- **Dificultad**: BAJA

#### N1.3 — Security Definitions [FUNDACIONAL]
- **Archivos**: `SuperHash/Crypto/SecurityDefs.lean` (nuevo)
- **Deps**: N1.1
- **Source**: Copiar `LeanHash/SecurityDefs.lean` (13 theorems) + `BirthdayBound.lean` (9 thms) + `GeneralizedBirthday.lean` (13 thms) + `JouxMulticollision.lean` (9 thms)
- **Entregables**:
  - `SecurityLevel`, `HashParams`, `CICOParams` structures
  - `birthday_bound`, `collision_leq_half_output`, `gbp_better_than_birthday`, `joux_complexity_linear_in_k`
  - ~44 theorems totales de 4 archivos LeanHash
- **Dificultad**: BAJA (copy)

#### N1.4 — SPNDegree + IdealDegree [PARALELO]
- **Archivos**: `SuperHash/Crypto/SPNDegree.lean`, `SuperHash/Crypto/IdealDegree.lean` (nuevos)
- **Deps**: N1.1
- **Source**: Copiar `LeanHash/SPNDegree.lean` (10 thms) + `LeanHash/IdealDegree.lean` (11 thms)
- **Entregables**:
  - `sbox_degree`, `full_round_degree`, `totalDegreeUpperBound`, `more_rounds_higher_degree`
  - `idealDegreebound`, `ideal_degree_mono_rounds`, `positive_margin_implies_security`
  - ~21 theorems
- **Dificultad**: BAJA

#### N1.5 — Concrete Instances + Smoke Tests [HOJA]
- **Archivos**: `SuperHash/Crypto/Instances.lean` (nuevo)
- **Deps**: N1.1, N1.2, N1.3, N1.4
- **Source**: Copiar `LeanHash/SboxInstances.lean` + `LeanHash/DesignSpace.lean` instances
- **Entregables**:
  - AES/PRESENT/Poseidon S-box params verificados
  - `aes128Design`, `poseidon128Design` con métricas reales
  - `#eval` smoke tests
  - ~10 concrete verifications

### Fase 2: S-box Certification + BitVec

#### N2.1 — DDT Computation [FUNDACIONAL] ⚠️ DE-RISK
- **Archivos**: `SuperHash/Crypto/DDT.lean` (nuevo)
- **Deps**: N1.1
- **Dificultad**: MEDIA
- **Entregables**:
  - `def DDT (sbox : Fin (2^n) → Fin (2^n)) (a b : Fin (2^n)) : Nat` — via counting
  - `def diffUniformity (sbox) : Nat := max over DDT`
  - `def LAT (sbox) (a b : Fin (2^n)) : Int` — Linear Approximation Table (QA #4)
  - Concrete: AES DDT verified via `native_decide` (D16)
  - DE-RISK: probar primero con 4-bit S-box (16×16 table), luego 8-bit
- **Source**: TrustHash/Sbox/AutoSboxPipeline.lean (pattern `native_decide` con lookup tables)

#### N2.2 — SboxCertifiedParams [CRITICO]
- **Archivos**: `SuperHash/Crypto/SboxCertified.lean` (nuevo)
- **Deps**: N2.1, N1.1
- **Dificultad**: MEDIA
- **Source**: Adaptar `TrustHash/Sbox/SboxCertifiedParams.lean`
- **Entregables**:
  - `structure SboxCertified` (inputBits, delta, nl, degree + proofs de bounds)
  - Bridge: `SboxCertified → SboxParams` (extracción de parámetros)
  - `aesCertified : SboxCertified` (δ=4, NL=112, deg=7 — proven)
  - `presentCertified : SboxCertified` (δ=4, NL=4, deg=3 — proven)

#### N2.3 — AutoSboxPipeline [CRITICO]
- **Archivos**: `SuperHash/Crypto/AutoSbox.lean` (nuevo)
- **Deps**: N2.1, N2.2
- **Dificultad**: MEDIA
- **Source**: Adaptar `TrustHash/Sbox/AutoSboxPipeline.lean`
- **Entregables**:
  - `def generateCert : ConcreteSbox → SboxCertified` — auto-certifica DDT, LAT, degree
  - `theorem generateCert_valid` — certificado es correcto
  - End-to-end: concrete S-box table → certified params

#### N2.4 — Certified Instances [HOJA]
- **Archivos**: `SuperHash/Crypto/CertInstances.lean` (nuevo)
- **Deps**: N2.3
- **Entregables**:
  - AES, PRESENT, Poseidon S-box certifications completas
  - `#eval` pipeline demos
  - Non-vacuity: `example` instanciando todas las hypotheses

### Fase 3: CryptoSemantics (The Core Gap)

#### N3.1 — CryptoSemantics Structure [FUNDACIONAL] ⚠️ DE-RISK
- **Archivos**: `SuperHash/Crypto/Semantics.lean` (nuevo)
- **Deps**: N1.3, N2.2
- **Dificultad**: MEDIA
- **Entregables**:
  - `structure CryptoSemantics` (D14: 7 campos)
  - `instance : Inhabited CryptoSemantics` (default = all zeros)
  - `instance : DecidableEq CryptoSemantics`
  - `instance : BEq CryptoSemantics`
  - `def dominates : CryptoSemantics → CryptoSemantics → Prop` (copiar de LeanHash, D17)
  - DE-RISK: compilar structure + instances antes de continuar

#### N3.2 — evalCryptoSem [FUNDACIONAL]
- **Archivos**: `SuperHash/Crypto/CryptoEval.lean` (nuevo)
- **Deps**: N3.1
- **Dificultad**: MEDIA
- **Entregables**:
  - `def evalCryptoSem : CryptoOp → List CryptoSemantics → CryptoSemantics`
  - Semántica por operación (D15 — sequential vs parallel distintos):
    - `sbox(d, child)` → `{deg = d * child.deg, δ = child.δ, ...}`
    - `compose(f, s)` → `{deg = f.deg * s.deg, δ = domain-specific, latency = f.lat + s.lat, ...}` (sequential)
    - `parallel(l, r)` → `{deg = max(l.deg, r.deg), δ = max(l.δ, r.δ), ...}`
    - `iterate(n, body)` → `{deg = body.deg^n, activeSboxes = n * body.activeSboxes, ...}`
    - Block constructors: compositional via bridge theorems
  - Guards: `exponent ≥ 1` para pow (L-550)

#### N3.3 — NodeSemantics Instance [CRITICO]
- **Archivos**: `SuperHash/Crypto/NodeSemInstance.lean` (nuevo)
- **Deps**: N3.2
- **Dificultad**: MEDIA
- **Entregables**:
  - `instance : NodeSemantics CryptoOp CryptoSemantics`
  - Proofs: `evalOp_ext`, `evalOp_mapChildren`, `evalOp_skeleton`
  - Pattern: L-458 (concrete evalOp, no typeclass dispatch)

#### N3.4 — NatBridge (Backward Compatibility) [CRITICO]
- **Archivos**: `SuperHash/Crypto/NatBridge.lean` (nuevo)
- **Deps**: N3.2
- **Dificultad**: MEDIA
- **Entregables**:
  - `def projectToNat : CryptoSemantics → Nat := fun cs => cs.algebraicDegree`
  - `theorem natBridge_agrees : ∀ op args, projectToNat (evalCryptoSem op (args.map liftNat)) = evalCryptoOp op (args.map id)`
  - Garantiza que v2.0 tests siguen pasando (D20)

#### N3.5 — ConsistentCryptoValuation [CRITICO]
- **Archivos**: `SuperHash/Crypto/CryptoConsistency.lean` (nuevo)
- **Deps**: N3.3
- **Dificultad**: ALTA
- **Entregables**:
  - `def ConsistentCryptoValuation : EGraph CryptoOp → (Nat → CryptoSemantics) → (EClassId → CryptoSemantics) → Prop`
  - Preservation theorems: merge, add, rebuild preservan CV
  - Source: adaptar v2.0 Consistency.lean para CryptoSemantics

#### N3.6 — Integration Tests + Non-vacuity [HOJA]
- **Archivos**: `SuperHash/Crypto/SemTests.lean`, `Tests/NonVacuity/CryptoSem.lean` (nuevos)
- **Deps**: N3.5, N5.4 (optional — degree integration)
- **Entregables**:
  - `#eval` tests: evalCryptoSem en diseños concretos produce métricas razonables
  - Non-vacuity: ConsistentCryptoValuation satisfacible con diseño concreto
  - v2.0 regression: NatBridge pasa para todos los tests existentes

### Fase 4: Crypto Rewrite Rules

#### N4.1 — CryptoSoundRule Framework [FUNDACIONAL]
- **Archivos**: `SuperHash/Crypto/CryptoRule.lean` (nuevo)
- **Deps**: N3.3
- **Dificultad**: MEDIA
- **Entregables**:
  - `structure CryptoSoundRule` extends SoundRewriteRule with:
    - `securityPreserved : ∀ env, dominates (eval rhs env) (eval lhs env)` (D17)
    - o `securityEquivalent : ∀ env, metricsEq (eval lhs env) (eval rhs env)`
  - Clasificación: equivalence | improvement (con dominates direction)
  - Source: adaptar TrustHash/HashSoundRules.lean pattern

#### N4.2 — SboxSubstitute Rule [CRITICO]
- **Archivos**: `SuperHash/Crypto/Rules/SboxSubstitute.lean` (nuevo)
- **Deps**: N4.1, N1.1
- **Dificultad**: MEDIA
- **Entregables**:
  - `SPN(s1,l,r) → SPN(s2,l,r)` si `δ(s2) ≤ δ(s1) ∧ deg(s2) ≥ deg(s1)`
  - Soundness proof: uses SboxProperties monotonicity theorems
  - Non-vacuity: AES S-box → better S-box (if exists)

#### N4.3 — RoundReduce Rule [CRITICO]
- **Archivos**: `SuperHash/Crypto/Rules/RoundReduce.lean` (nuevo)
- **Deps**: N4.1, N1.2
- **Dificultad**: MEDIA
- **Entregables**:
  - `SPN(s,l,r) → SPN(s,l,r-1)` si `securityBound(s,l,r-1) ≥ target`
  - Soundness: wide_trail_lower_bound + activeMinSboxes ≥ threshold
  - Guard: `r > 1` (prevent zero rounds)

#### N4.4 — WideTrailImprove Rule [CRITICO]
- **Archivos**: `SuperHash/Crypto/Rules/WideTrailImprove.lean` (nuevo)
- **Deps**: N4.1, N1.2
- **Dificultad**: MEDIA
- **Entregables**:
  - `SPN(s,l1,r) → SPN(s,l2,r')` si `BN(l2) > BN(l1)` y `r' < r` (fewer rounds needed)
  - Soundness: `more_rounds_more_active` + `wide_trail_lower_bound`

#### N4.5 — SboxCompose Rule [CRITICO]
- **Archivos**: `SuperHash/Crypto/Rules/SboxCompose.lean` (nuevo)
- **Deps**: N4.1
- **Dificultad**: BAJA
- **Entregables**:
  - `sbox(sbox(x, d1), d2) → sbox(x, d1*d2)` (degree multiplication)
  - Source: copiar `TrustHash/HashSoundRules.lean` sboxCompose_sound pattern
  - Soundness: `deg(S2 ∘ S1) ≤ deg(S2) * deg(S1)`

#### N4.6 — RoundsCompose Rule [CRITICO]
- **Archivos**: `SuperHash/Crypto/Rules/RoundsCompose.lean` (nuevo)
- **Deps**: N4.1
- **Dificultad**: BAJA
- **Entregables**:
  - `compose(rounds(c,r1), rounds(c,r2)) → rounds(c,r1+r2)`
  - Source: copiar TrustHash roundsCompose pattern
  - Soundness: `activeSboxes(r1+r2) = activeSboxes(r1) + activeSboxes(r2)`

#### N4.7 — Rule Non-vacuity [HOJA]
- **Archivos**: `Tests/NonVacuity/CryptoRules.lean` (nuevo)
- **Deps**: N4.2-N4.6
- **Entregables**:
  - Concrete examples para cada regla con parámetros AES/Poseidon
  - Verificar que precondiciones son satisfacibles
  - `#eval` smoke tests

### Fase 5: Algebraic Degree (Crown Jewel)

#### N5.1 — ANF + IsPermutation [FUNDACIONAL] ⚠️ DE-RISK
- **Archivos**: `SuperHash/Crypto/ANF.lean` (nuevo)
- **Deps**: N1.4
- **Dificultad**: ALTA
- **Entregables**:
  - `def ANF` — Algebraic Normal Form representation (polynomial over GF(2))
  - `def IsPermutation (f : Fin (2^n) → Fin (2^n)) : Prop` (D18: bijection)
  - `def algebraicDegree : ANF → Nat` — max monomial degree
  - DE-RISK: compilar definitions + 1 concrete example antes de continuar
- **Source**: Boura-Canteaut 2011, Section 2

#### N5.2 — Degree Properties [FUNDACIONAL]
- **Archivos**: `SuperHash/Crypto/AlgebraicDegree.lean` (nuevo)
- **Deps**: N5.1
- **Dificultad**: MEDIA
- **Entregables**:
  - `theorem degree_upper_bound_n : algebraicDegree f ≤ n` (for f : Fin 2^n → Fin 2^n)
  - `theorem degree_composition_upper : algebraicDegree (g ∘ f) ≤ algebraicDegree g * algebraicDegree f`
  - `theorem degree_xor : algebraicDegree (f ⊕ g) ≤ max (algebraicDegree f) (algebraicDegree g)`

#### N5.3 — Boura-Canteaut Bound [CRITICO] ⚠️ DE-RISK
- **Archivos**: `SuperHash/Crypto/DegreeComposition.lean` (nuevo)
- **Deps**: N5.2
- **Dificultad**: MUY_ALTA
- **Entregables**:
  - `theorem bouraCanteutBound (F G : Fin (2^n) → Fin (2^n)) (hPerm : IsPermutation F) : algebraicDegree (G ∘ F) ≤ n - Nat.ceil ((n - algebraicDegree G) / algebraicDegree (inverse F))`
  - **NOTA**: Puede requerir sorry inicial — el proof usa teoría de codificación (divisor bound)
  - Source: Boura-Canteaut 2011, Theorem 1
- **Plan de fallback**: probar caso especial primero (`deg(F⁻¹) = n-1` para bijective S-box), generalizar después

#### N5.4 — Degree-Round Security [CRITICO]
- **Archivos**: `SuperHash/Crypto/DegreeSecurity.lean` (nuevo)
- **Deps**: N5.3 (o N5.2 si sorry en N5.3)
- **Dificultad**: MEDIA
- **Entregables**:
  - `theorem degree_increases_with_rounds` — more rounds → higher algebraic degree
  - `theorem degree_security_margin` — degree > threshold → attack infeasible
  - Connects to CryptoSemantics.algebraicDegree field

#### N5.5 — AES Degree Verification [HOJA]
- **Archivos**: `Tests/NonVacuity/AlgebraicDegree.lean` (nuevo)
- **Deps**: N5.4
- **Entregables**:
  - `example : IsPermutation aes_sbox` — AES S-box is permutation (D18)
  - `example : algebraicDegree aes_sbox = 7` — AES has degree 7 over 8 bits
  - Non-vacuity para Boura-Canteaut (si proven) con AES params

### Fase 6: Pipeline Integration + Fitness

#### N6.1 — Fitness Function [FUNDACIONAL]
- **Archivos**: `SuperHash/Crypto/Fitness.lean` (nuevo)
- **Deps**: N1.3
- **Dificultad**: BAJA
- **Entregables** (D19 — formal bounds):
  - `def genericFloor : HashParams → Nat` — min(birthday, GBP, Joux)
  - `def differentialBound : SboxCertified → MDSParams → Nat → Nat` — from δ + active sboxes
  - `def degreeSecurity : Nat → Nat → Nat` — from degree + treewidth (if available)
  - `def securityLevel := min genericFloor (min differentialBound degreeSecurity)`
  - `theorem fitness_monotone` — security monotone in each component
- **Source**: LeanHash/SecurityDefs.lean + LeanHash/BirthdayBound.lean

#### N6.2 — Crypto Saturation [CRITICO]
- **Archivos**: `SuperHash/Pipeline/CryptoSaturate.lean` (nuevo)
- **Deps**: N4.7, N3.5
- **Dificultad**: MEDIA
- **Entregables**:
  - `def saturateCrypto : EGraph CryptoOp → List CryptoSoundRule → Nat → EGraph CryptoOp`
  - `theorem saturateCrypto_preserves_consistency` — ConsistentCryptoValuation preserved
  - `theorem saturateCrypto_preserves_security` — all rules are CryptoSoundRule → security preserved
- **Source**: Adaptar TrustHash/EGraph/RealSaturate.lean pattern

#### N6.3 — Crypto Extraction [CRITICO]
- **Archivos**: `SuperHash/Pipeline/CryptoExtract.lean` (nuevo)
- **Deps**: N6.2, N5.4
- **Dificultad**: MEDIA
- **Entregables**:
  - `def extractCryptoPareto : EGraph CryptoOp → Fitness → List (CryptoExpr × CryptoSemantics)`
  - Extraction uses CryptoSemantics cost (not Nat cost)
  - Pareto over real security metrics (6D dominance)

#### N6.4 — Pipeline v2.5 Composition [CRITICO]
- **Archivos**: `SuperHash/Pipeline/PipelineV25.lean` (nuevo)
- **Deps**: N6.2, N6.3, N6.1
- **Dificultad**: MEDIA
- **Entregables**:
  - `def superhash_v25 : List CryptoSoundRule → EGraph CryptoOp → PipelineConfig → PipelineResult`
  - Compose: saturateCrypto → computeFitness → extractCryptoPareto
  - Pipeline soundness: each stage preserves invariant (L-513)

#### N6.5 — Master Theorem v2.5 [CRITICO]
- **Archivos**: `SuperHash/Pipeline/MasterTheoremV25.lean` (nuevo)
- **Deps**: N6.4
- **Dificultad**: ALTA
- **Entregables**:
  - `theorem pipeline_soundness_v25` — 4-part:
    1. Semantic correctness: extracted designs evaluate to root CryptoSemantics
    2. Pareto optimality: no design dominated by another (over CryptoSemantics)
    3. Security floor: fitness(design) ≥ genericFloor
    4. Rule soundness: all applied rules are CryptoSoundRule
  - Non-vacuity: `example` instanciando TODAS las hipótesis

#### N6.6 — E2E Demo + Non-vacuity [HOJA]
- **Archivos**: `SuperHash/Instances/CryptoDemo.lean`, `Tests/NonVacuity/PipelineV25.lean` (nuevos)
- **Deps**: N6.5
- **Entregables**:
  - AES design → saturate with crypto rules → extract Pareto → evaluate fitness
  - Compare fitness before/after saturation
  - Non-vacuity para master theorem v2.5

---

## Orden Topológico (Bloques de Ejecución)

| Bloque | Nodos | Tipo | Ejecución | Deps |
|--------|-------|------|-----------|------|
| **B1** | N1.1, N1.2, N1.3 | FUND (copy) | Paralelo | — |
| **B2** | N1.4 | PARALELO (copy) | Secuencial | B1 |
| **B3** | N1.5 | HOJA | Secuencial | B1, B2 |
| **B4** | N2.1 | FUND ⚠️ | Secuencial | B1 |
| **B5** | N2.2 | CRITICO | Secuencial | B4 |
| **B6** | N2.3, N2.4 | CRIT+HOJA | Paralelo | B5 |
| **B7** | N3.1 | FUND ⚠️ | Secuencial | B1, B5 |
| **B8** | N3.2 | FUND | Secuencial | B7 |
| **B9** | N3.3, N3.4 | CRITICO | Paralelo | B8 |
| **B10** | N3.5 | CRITICO | Secuencial | B9 |
| **B11** | N3.6 | HOJA | Secuencial | B10 |
| **B12** | N4.1 | FUND | Secuencial | B9 |
| **B13** | N4.2, N4.3, N4.4 | CRITICO | Paralelo | B12 |
| **B14** | N4.5, N4.6 | CRITICO | Paralelo | B12 |
| **B15** | N4.7 | HOJA | Secuencial | B13, B14 |
| **B16** | N5.1 | FUND ⚠️ | Secuencial | B2 |
| **B17** | N5.2 | FUND | Secuencial | B16 |
| **B18** | N5.3 | CRIT ⚠️ | Secuencial | B17 |
| **B19** | N5.4, N5.5 | CRIT+HOJA | Paralelo | B18 |
| **B20** | N6.1 | FUND | Secuencial | B1 |
| **B21** | N6.2 | CRITICO | Secuencial | B15, B10 |
| **B22** | N6.3 | CRITICO | Secuencial | B21, B19 |
| **B23** | N6.4, N6.5 | CRITICO | Secuencial | B22, B20 |
| **B24** | N6.6 | HOJA | Secuencial | B23 |

**Total v2.5**: 24 bloques, 30 nodos, ~20 archivos Lean nuevos.

**Paralelismo**: B16-B19 (Fase 5) puede ejecutarse en paralelo con B7-B15 (Fases 3-4). Convergencia en B22.

---

## Árbol de Progreso

```
SuperHash v2.5
├── Fase 1: Crypto Foundations (Copy LeanHash — ~55 thms)
│   ├── [ ] B1: N1.1 SboxParams | N1.2 MDS | N1.3 SecurityDefs (COPY)
│   ├── [ ] B2: N1.4 SPNDegree + IdealDegree (COPY)
│   └── [ ] B3: N1.5 Concrete Instances
│
├── Fase 2: S-box Certification + BitVec (Adapt TrustHash)
│   ├── [ ] B4: N2.1 DDT Computation ⚠️ DE-RISK (native_decide)
│   ├── [ ] B5: N2.2 SboxCertifiedParams
│   └── [ ] B6: N2.3 AutoSboxPipeline | N2.4 Certified Instances
│
├── Fase 3: CryptoSemantics (THE CORE GAP)
│   ├── [ ] B7: N3.1 CryptoSemantics Structure ⚠️ DE-RISK
│   ├── [ ] B8: N3.2 evalCryptoSem (sequential vs parallel)
│   ├── [ ] B9: N3.3 NodeSemantics Instance | N3.4 NatBridge
│   ├── [ ] B10: N3.5 ConsistentCryptoValuation
│   └── [ ] B11: N3.6 Smoke Tests + Non-vacuity
│
├── Fase 4: Crypto Rewrite Rules (Real Proofs)
│   ├── [ ] B12: N4.1 CryptoSoundRule Framework
│   ├── [ ] B13: N4.2 SboxSubstitute | N4.3 RoundReduce | N4.4 WideTrailImprove
│   ├── [ ] B14: N4.5 SboxCompose | N4.6 RoundsCompose
│   └── [ ] B15: N4.7 Rule Non-vacuity
│
├── Fase 5: Algebraic Degree (Crown Jewel) ‖ parallel with Fases 3-4
│   ├── [ ] B16: N5.1 ANF + IsPermutation ⚠️ DE-RISK
│   ├── [ ] B17: N5.2 Degree Properties
│   ├── [ ] B18: N5.3 Boura-Canteaut Bound ⚠️ (MUY_ALTA, may sorry)
│   └── [ ] B19: N5.4 Degree-Round Security | N5.5 AES Degree
│
└── Fase 6: Pipeline + Fitness Integration
    ├── [ ] B20: N6.1 Fitness Function (formal bounds)
    ├── [ ] B21: N6.2 Crypto Saturation
    ├── [ ] B22: N6.3 Crypto Extraction
    ├── [ ] B23: N6.4 Pipeline v2.5 | N6.5 Master Theorem v2.5
    └── [ ] B24: N6.6 E2E Demo + Non-vacuity
```

---

## Riesgos y Mitigaciones

| # | Riesgo | Nivel | Mitigación |
|---|--------|-------|-----------|
| R1 | Boura-Canteaut (N5.3) MUY_ALTA | CRITICO | Caso especial primero (deg(F⁻¹)=n-1), sorry si necesario |
| R2 | CryptoSemantics cascading impact | ALTO | NatBridge (D20) mantiene v2.0 tests |
| R3 | Composición sequential vs parallel (D15) | ALTO | QA #1 resolved: operaciones distintas |
| R4 | native_decide timeout 8-bit DDT | MEDIO | DE-RISK con 4-bit primero (B4) |
| R5 | TrustHash version mismatch | MEDIO | Copiar, no importar — adapt types |
| R6 | ConsistentCryptoValuation proof (N3.5) | ALTO | Copiar pattern de v2.0 Consistency.lean |
| R7 | IsPermutation proof for AES S-box | MEDIO | native_decide en Fin 256 → Fin 256 |
| R8 | 0^0=1 en exponentes (L-550) | MEDIO | Guards `exponent ≥ 1` obligatorios |

---

## QA Issues Incorporados (v2.5)

| # | Issue (Gemini QA) | Resolución |
|---|-------------------|------------|
| 1 | Composición conflates sequential/parallel | D15: operaciones distintas en evalCryptoSem |
| 2 | bv_decide intractable para 8-bit | D16: native_decide con lookup tables |
| 3 | Missing dominates in CryptoSoundRule | D17: dominates incluido en framework |
| 4 | Missing LAT / linear bias field | D14: linearBias añadido a CryptoSemantics |
| 5 | Unjustified fitness function | D19: composición de bounds formalizados |
| 6 | Missing IsPermutation for Boura-Canteaut | D18: IsPermutation en N5.1 |
| 7 | Type mismatch LeanHash↔SuperHash | N1.x incluye type adaptation |
| 8 | N5.4→N3.2 missing dependency | DAG actualizado |
| 9 | B20 packed too tight | Split into B20-B22 |
| 10 | v2.0 test migration | D20: NatBridge + explicit regression in N3.6 |
| 11 | 21 blocks aggressive | Merged B1 (3 copy nodes paralelo) |

---

## Librerías Reutilizables — Mapping Exacto

### De LeanHash (copiar/adaptar)

| Archivo LeanHash | → Archivo SuperHash | Teoremas | Adaptación |
|------------------|---------------------|----------|-----------|
| SboxProperties.lean | Crypto/SboxProperties.lean | 12 | Tipos: Nat fields |
| MDSMatrix.lean | Crypto/MDSProperties.lean | 9 | Tipos: MDSParams |
| SecurityDefs.lean | Crypto/SecurityDefs.lean | 13 | Directa |
| BirthdayBound.lean | Crypto/SecurityDefs.lean | 9 | Merge |
| GeneralizedBirthday.lean | Crypto/SecurityDefs.lean | 13 | Merge |
| JouxMulticollision.lean | Crypto/SecurityDefs.lean | 9 | Merge |
| SPNDegree.lean | Crypto/SPNDegree.lean | 10 | Directa |
| IdealDegree.lean | Crypto/IdealDegree.lean | 11 | Directa |
| SboxInstances.lean | Crypto/Instances.lean | 10 | Directa |
| DesignSpace.lean | Crypto/Semantics.lean (parcial) | 23 | Adaptar structures |
| **Total** | | **~119** | |

### De TrustHash (adaptar patrones)

| Módulo TrustHash | → Uso en SuperHash | Patrón |
|------------------|---------------------|--------|
| HashSoundRules.lean | Crypto/CryptoRule.lean | Pattern: rule + soundness pair |
| Sbox/SboxCertifiedParams.lean | Crypto/SboxCertified.lean | Structure + bridge |
| Sbox/AutoSboxPipeline.lean | Crypto/AutoSbox.lean | native_decide pipeline |
| EGraph/RealSaturate.lean | Pipeline/CryptoSaturate.lean | Fixpoint saturation loop |
| EGraph/PipelineSoundness.lean | Pipeline/PipelineV25.lean | Compositional soundness |
| DP/TreewidthDP.lean | (future v3.0) | Tree DP execution |

---

## Lecciones Aplicables

| ID | Título | Aplicación v2.5 |
|----|--------|-----------------|
| L-513 | Compositional E2E Proofs | Pipeline v2.5 composition (~30 líneas) |
| L-458 | Concrete evalOp | evalCryptoSem concreto, no typeclass |
| L-376 | Total Val semantics | CryptoSemantics con Inhabited, no Option |
| L-550 | 0^0=1 guard | Guards en iterate deg^r |
| L-465 | NodeSemantics mismatch | NO forzar OptiSat instance |
| L-523 | Library adaptation | Copy LeanHash: esperar ≤1 bug/700 LOC |
| L-659 | Non-recursive semantics | Fitness evaluation sin loops internos |
| L-617 | #eval as oracle | 10+ smoke tests antes de proof formal |
