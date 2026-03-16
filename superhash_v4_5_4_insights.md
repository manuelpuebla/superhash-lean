# Insights: SuperHash v5.0 Features — S-box Search, Substitution Rules, Performance, GF(2^n), Attacks

**Fecha**: 2026-03-16
**Dominio**: lean4
**Estado**: upgrade (v4.5.3 → v5.0 features)

## 1. Análisis del Objeto de Estudio

5 features gap identificados vs superhash_idea.md:
1. **S-box search autónomo** — pipeline de certificación existe (AutoSboxPipeline), falta búsqueda/generación
2. **Reglas de sustitución** — `sboxSubstituteStrategy` existe para grado, falta `δ`-based swap
3. **Performance model real** — latency/gateCount integrados en CryptoSemantics, son abstractos (Nat)
4. **GF(2^n) formal** — TrustHash tiene `BitVec4Arith.lean` para GF(2^4), falta GF(2^8)
5. **Ataques no modelados** — slide, integral, impossible diff, invariant subspace, quantum

## 2. Lecciones Aplicables

### Críticas para implementación
- **L-546**: ConditionalRewriteRule pattern — extender con backward_compat para reglas de sustitución
- **L-513**: Compositional End-to-End Proofs — S-box search como pipeline: generar → certificar → extraer
- **L-415**: Proof-Carrying Data Structures — SearchResult que empaca (sbox, properties, proof)
- **L-544**: Constraint graph K_n modeling — treewidth para análisis de complejidad de búsqueda
- **L-566**: Bool-to-Prop bridge — verificación de tablas S-box via Bool checker + native_decide
- **L-688**: Nonlinear Nat arithmetic — expansión manual para cotas diferenciales cuadráticas

### Anti-patrones
- NUNCA `0^0` sin guardia en patrones pow (L-550)
- NUNCA example-based verification para propiedades estructurales (L-351)
- NUNCA native_decide en structs con proof fields (L-199)

## 3. Código Reutilizable de LeanHash y TrustHash

### TrustHash v5.0 — Componentes NUEVOS para copiar

| Módulo | LOC | Teoremas | Feature |
|--------|-----|----------|---------|
| **Attacks/AG/** (5 files) | 1,152 | ~40 | Quantum AG bounds (Feng-Ling-Xing), drinfeld_vladut |
| **Attacks/Composition/** (9 files) | 3,500 | ~80 | Attack E-graph: Core + EMatch + Saturate + Extract + 15 rules |
| **Math/{AGDistribution,InverseSieve,VarietyBounds}** | 707 | ~30 | Collision variety theory, Hilbert codimension |
| **Attacks/CollisionVariety/** | 381 | ~15 | VarietySpec, collision lower bounds |
| **Attacks/FullVerdictV5.lean** | 462 | ~20 | `overallSecurityV5 = min(quantumAGFloor, expandedStructuralCostV5)` |
| **Attacks/SuperHashInterface.lean** | 176 | ~8 | VerdictExport, integration bridge |
| **Sbox/BitVec4Arith.lean** | ~200 | ~15 | GF(2^4) arithmetic verified by decide |
| **Sbox/SboxFullCert.lean** | ~200 | ~12 | Unified S-box certification pipeline |

**Total para copiar**: ~6,800 LOC, ~220 teoremas

### TrustHash v4.0 — Ataques ya formalizados

| Ataque | Módulo | Status |
|--------|--------|--------|
| Differential (char, truncated, boomerang, impossible) | Composition/Rules/Differential | ✅ 5 rules |
| Linear (hull, trail, Matsui) | Composition/Rules/Linear | ✅ 2 rules |
| Structural (MITM, rebound, zero-sum) | Composition/Rules/Structural | ✅ 3 rules |
| Slide attack | Attacks/SlideAttack/Spec | ✅ Formalized |
| Related-key | Attacks/RelatedKey/ | ✅ Formalized |
| Invariant subspace | Attacks/InvariantSubspace/Spec | ✅ Formalized |
| Division property | Attacks/DivisionProperty/Spec | ✅ MILP + propagation |
| Constant-time | ConstantTime/Spec | ✅ Formalized |
| Grover quantum | QuantumBounds | ✅ Formalized |
| AG quantum | Attacks/AG/Bounds | ✅ v5.0 NEW |

### LeanHash — Referencia teórica

| Módulo | Teoremas | Uso |
|--------|----------|-----|
| SboxProperties.lean | 11 | Bounds teóricos: δ ≤ 2^n, APN, bent NL, deg ≥ n-1 |
| SboxInstances.lean | 10 | AES/PRESENT/Poseidon params certificados |
| BouraCanteutBound.lean | 66 | BCD11/BC13, iterated bounds |
| HigherOrderDiff.lean | 64 | Zero-sum, vanishing subspace |
| LinearLayerDegree.lean | 84 | SPN degree tracking |

### SuperHash actual — Infraestructura existente

| Componente | Status | Sustitución-ready? |
|------------|--------|-------------------|
| S-box certification (AutoSboxPipeline) | ✅ Completo | ✅ |
| `sboxSubstituteStrategy` (degree swap) | ✅ Existe | ✅ (falta δ-based) |
| AttackOp (12 tipos) | ✅ Definido | ✅ |
| CryptoSemantics (7 campos incl. latency, gateCount) | ✅ Integrado | ✅ |
| Pareto 6D | ✅ Completo | ✅ |

## 4. Bibliografía Relevante

### Papers clave (ya en biblioteca)

**S-box search**:
- Lu et al. "STP-based model toward designing S-boxes" — SMT constraint solving
- Kuznetsov et al. "Evolutionary Approach to S-box Generation" — GA optimization
- Canteaut et al. "Construction of Lightweight S-Boxes using Feistel/MISTY" — structured generation

**Ataques**:
- StarkWare "STARK-Friendly Hash" — integral, impossible differential, zero-sum on GMiMC
- Ashur-Buschman-Mahzoun "Algebraic Cryptanalysis of HADES" — Gröbner attacks
- Merz-Rodriguez "Skipping Class" — round-skipping attacks via matrix structure

### Gaps bibliográficos
- ❌ Slide attacks (papers dedicados)
- ❌ Invariant subspace attacks (papers dedicados) — pero TrustHash YA tiene formalización
- ❌ Hardware FPGA cost models formales
- ❌ S-box search complexity models

## 5. Nueva Bibliografía

Sección omitida (--skip-online)

## 6. Insights de Nueva Bibliografía

Sección omitida (sin descargas nuevas)

## 7. Síntesis de Insights

### Hallazgos clave (Top 10)

1. **TrustHash v5.0 tiene TODOS los ataques formalizados** que SuperHash necesita — slide, invariant subspace, division property, etc. Solo hay que copiar/adaptar (~6.8K LOC).

2. **S-box substitution ya funciona** — `sboxSubstituteStrategy` en CryptoRules.lean sustituye por grado. Extender a δ-based es mecánico: agregar condición `differentialUniformity(new) ≤ differentialUniformity(old)`.

3. **Búsqueda autónoma de S-boxes es factible** usando la infraestructura existente: `AutoSboxPipeline` certifica cualquier S-box table → generar candidatos (exhaustivo para 4-bit, heurístico para 8-bit) → filtrar por Pareto (δ, NL, deg, gates).

4. **GF(2^4) ya existe** en TrustHash (`BitVec4Arith.lean`). GF(2^8) requiere extensión o tabla lookup (como AES S-box). Para 8-bit, `native_decide` es impracticable (2^256 cases) → usar tabla + certificate.

5. **Performance model es razonable** como está: latency/gateCount en CryptoSemantics son abstractos pero compositionales. Un "performance model real" requeriría benchmarks de hardware específico, que está fuera del scope de verificación formal.

6. **La composable attack engine de TrustHash v5.0** es exactamente lo que SuperHash necesita para el duel framework — copiar Composition/ entero y conectar con DuelLoop.

7. **Regla de sustitución `SPN(s₁) ⟹ SPN(s₂)` si δ(s₂) < δ(s₁)`** es implementable como `ConditionalRewriteRule` (L-546) con `sideCond = differentialUniformity(new) ≤ differentialUniformity(old) ∧ algebraicDegree(new) ≥ algebraicDegree(old)`.

8. **El verdict v5.0 de TrustHash** (`overallSecurityV5 = min(quantumAGFloor, expandedStructuralCostV5)`) es un upgrade directo de `computeFullVerdict` actual. Copiar y adaptar.

9. **Los 28 archivos nuevos de TrustHash v5.0** (commit 2274591) son modulares y autocontenidos — diseñados específicamente para integración con SuperHash.

10. **Para ataques no modelados**: NO necesitamos papers nuevos ni investigación — TrustHash ya los formalizó. Solo hay que copiar: SlideAttack/Spec, RelatedKey/, InvariantSubspace/Spec, DivisionProperty/Spec.

### Riesgos identificados

| Riesgo | Mitigación |
|--------|-----------|
| 6.8K LOC de copia puede introducir conflictos de namespace | Adaptar namespaces al copiar, no importar |
| GF(2^8) exhaustive es impracticable | Usar tabla + certificate (como AES S-box) |
| S-box search 8-bit es combinatoriamente intratable (2^256) | Heurístico: GA o constraint-based, no exhaustivo |
| Performance model "real" es indefinido | Mantener abstracto; agregar #eval benchmarks como proxy |
| ConditionalRewriteRule puede complicar saturación | Usar sideCond decidable para evitar bloqueo |

### Recomendaciones para planificación

**Fase 1 — Copy TrustHash v5.0 modules** (~6.8K LOC)
- Prioridad: Attacks/AG, Attacks/Composition, Math/*, FullVerdictV5, SuperHashInterface
- Adaptar namespaces, verificar build

**Fase 2 — S-box substitution rule** (~50 LOC)
- `ConditionalRewriteRule` con sideCond: `δ(new) ≤ δ(old) ∧ deg(new) ≥ deg(old)`
- Non-vacuity con AES S-box → S-box mejorada

**Fase 3 — S-box search framework** (~200 LOC)
- 4-bit: exhaustive (solo 16! = 2×10^13 bijections, pero factible con simetría)
- 8-bit: library of known S-boxes + certified params
- Pipeline: generate → AutoSboxPipeline → Pareto filter

**Fase 4 — Attack model integration** (~100 LOC)
- Copiar de TrustHash: SlideAttack, InvariantSubspace, DivisionProperty
- Integrar como nuevos constructores en `AttackOp` o como módulos separados
- Conectar con DuelLoop para Red team

**Fase 5 — Performance model upgrade** (~50 LOC)
- Agregar `circuitDepth : Nat` a CryptoSemantics (profundidad de circuito, no solo gates)
- #eval benchmarks para AES, Poseidon, PRESENT con valores reales
- Documentar: "performance metrics are abstract; real values require hardware benchmarks"

### Recursos prioritarios

1. TrustHash v5.0 commit 2274591 — 28 nuevos archivos
2. LeanHash SboxProperties.lean — bounds teóricos para validación
3. StarkWare STARK-Friendly Hash paper — referencia para integral/impossible attacks
4. Kuznetsov "Evolutionary S-box" — approach para búsqueda heurística
5. Lu "STP-based S-box" — constraint solving para generación
