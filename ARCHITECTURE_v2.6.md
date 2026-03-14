# SuperHash v2.6 — ARCHITECTURE

**Proyecto**: SuperHash v2.6
**Dominio**: Lean 4 (sin Mathlib)
**Base**: v2.5 complete (47 build jobs, 452 theorems, CryptoSemantics, DDT, fitness)
**Source**: LeanHash/UniversalHash.lean (Tyagi-Watanabe, 324 LOC, 18 theorems)
**Objetivo**: Integrar fundamentos information-theoretic en el pipeline crypto

---

## Visión

v2.6 reemplaza las heurísticas de seguridad con cotas information-theoretic formales de Tyagi-Watanabe. La conexión clave: la DDT de una S-box (ya computada en v2.5) determina la probabilidad de colisión, que el Leftover Hash Lemma traduce en bits de seguridad extraíbles.

---

## Decisiones Arquitecturales (v2.6)

### D21: LHL-based security replaces heuristic
**Justificación**: `differentialSecurityBits` usaba `activeSboxes * (n - log2(δ))` — heurística. El LHL da la cota exacta: seguridad = k - 2s donde k es la entropía de la fuente desde la DDT.

### D22: 2-UHF collision bound como constraint de diseño
**Justificación**: Las funciones hash en el E-graph deben satisfacer `P[F(x)=F(x')] ≤ 1/2^l`. Esto conecta la propiedad 2-UHF con la uniformidad diferencial δ/2^n.

### D23: ZK side-information degradation
**Justificación**: En circuitos ZK, el verifier ve información parcial (transcript). El Corollario 3 del LHL con side-info acota la pérdida: `security -= transcript_bits`.

---

## Fase Única: Information-Theoretic Integration

### N1 — Source Entropy from DDT [FUNDACIONAL]
- **Archivo**: `SuperHash/Crypto/SourceEntropy.lean` (nuevo)
- **Deps**: DDT.lean, Semantics.lean
- **Entregables**:
  - `def collisionProbFromDelta (delta n : Nat) : Nat := delta` (numerator, denominator = 2^n)
  - `def sourceEntropyBits (delta n activeSboxes : Nat) : Nat := activeSboxes * (n - ilog2 delta)` — same formula but now DERIVED from LHL, not heuristic
  - `theorem sourceEntropy_eq_differentialSecurity` — proves the existing `differentialSecurityBits` is exactly the LHL source entropy
  - `theorem sourceEntropy_mono_active` — monotone in active S-boxes
  - Copy key definitions from LeanHash/UniversalHash.lean: `differentialSourceEntropy`
- **Dificultad**: BAJA (definitions + bridge theorem)

### N2 — Extractor Length Bound [FUNDACIONAL]
- **Archivo**: `SuperHash/Crypto/ExtractorBound.lean` (nuevo)
- **Deps**: N1
- **Entregables**:
  - `def extractableBits (sourceEntropy securityBits : Nat) : Nat := sourceEntropy - 2 * securityBits`
  - `theorem extractor_bound_le_source` — l ≤ k (trivial: Nat.sub_le)
  - `theorem extractor_mono_entropy` — more source entropy → more extractable bits
  - `theorem birthday_is_extractor_bound` — birthdayFloor(n) = extractableBits(n, n/4) for uniform source
  - Concrete: AES (150 - 128 = 22 extra bits), SHA-256 (256 - 128 = 128), Poseidon (54 - 54 = 0)
- **Dificultad**: BAJA

### N3 — 2-UHF Collision Constraint [CRITICO]
- **Archivo**: `SuperHash/Crypto/UHFConstraint.lean` (nuevo)
- **Deps**: N1, DDT.lean
- **Entregables**:
  - `structure UHFDesignConstraint` — links DDT δ to 2-UHF collision bound
  - `def satisfiesUHF (delta n l : Nat) : Prop := delta * (2^l) ≤ 2^n` — the collision bound
  - `theorem ddt_implies_uhf` — if DDT max = δ and output = l ≤ n - ilog2(δ), then 2-UHF holds
  - `theorem aes_satisfies_uhf` — AES with δ=4, n=8: 4 * 2^6 = 256 = 2^8 ✓
  - Non-vacuity: PRESENT and AES concrete instances
- **Dificultad**: MEDIA

### N4 — Upgraded Fitness with LHL [CRITICO]
- **Archivo**: Modify `SuperHash/Crypto/Fitness.lean`
- **Deps**: N1, N2
- **Entregables**:
  - Add `lhlSecurityBits` as the information-theoretic version of `differentialSecurityBits`
  - `theorem lhl_agrees_with_differential` — proves the old heuristic = LHL bound (they're the same formula, now justified)
  - Update `fitness` docstring to cite Tyagi-Watanabe Theorem 1 as justification
  - Add `extractableSecurity` combining birthday floor + LHL + algebraic: `min(birthdayFloor, min(lhlBound, algebraicBound))`
- **Dificultad**: BAJA (the formula doesn't change, the justification does)

### N5 — ZK Side-Information Loss [CRITICO]
- **Archivo**: `SuperHash/Crypto/ZKSideInfo.lean` (nuevo)
- **Deps**: N2
- **Entregables**:
  - `def zkSecurityLoss (transcriptBits : Nat) : Nat := transcriptBits`
  - `def zkAdjustedSecurity (baseSecurity transcriptBits : Nat) : Nat := baseSecurity - transcriptBits`
  - `theorem zk_security_decreases` — security monotone decreasing in transcript length
  - `theorem poseidon_zk_vulnerability` — Poseidon with 54-bit base, 30-bit transcript → 24 effective bits (DANGER)
  - Concrete examples: STARK transcript sizes for Poseidon/Rescue
- **Dificultad**: BAJA
- **Source**: Tyagi-Watanabe Theorem 4 (LHL with side-info V: security degrades by |V| bits)

### N6 — Integration Tests + Non-vacuity [HOJA]
- **Archivo**: `Tests/NonVacuity/InfoTheoretic.lean` (nuevo)
- **Deps**: N3, N4, N5
- **Entregables**:
  - Non-vacuity: AES satisfies UHF constraint
  - Non-vacuity: LHL bound matches differentialSecurityBits
  - Non-vacuity: Poseidon ZK vulnerability detection
  - `#eval` smoke tests for all new functions

---

## DAG

```
N1 (SourceEntropy) ──→ N2 (ExtractorBound) ──→ N4 (Fitness upgrade)
         │                        │
         └──→ N3 (UHF Constraint) │
                                   └──→ N5 (ZK SideInfo)
                                              │
                                         N6 (Tests) ←── N3, N4, N5
```

## Bloques de Ejecución

| Bloque | Nodos | Tipo | Ejecución |
|--------|-------|------|-----------|
| **B1** | N1 | FUNDACIONAL | Secuencial |
| **B2** | N2, N3 | FUND+CRIT | Paralelo |
| **B3** | N4, N5 | CRITICO | Paralelo |
| **B4** | N6 | HOJA | Secuencial |

**Total v2.6**: 4 bloques, 6 nodos, ~4 archivos nuevos + 1 modificado.

---

## Estimación

| Archivo | LOC est. | Theorems est. | Sorry est. |
|---------|----------|---------------|-----------|
| SourceEntropy.lean | ~80 | 4 | 0 |
| ExtractorBound.lean | ~70 | 5 | 0 |
| UHFConstraint.lean | ~90 | 5 | 0 |
| Fitness.lean (mod) | +30 | 2 | 0 |
| ZKSideInfo.lean | ~70 | 4 | 0 |
| Tests/InfoTheoretic.lean | ~50 | 6 | 0 |
| **Total** | **~390** | **~26** | **0** |

---

## Riesgos

| Riesgo | Nivel | Mitigación |
|--------|-------|-----------|
| LHL formula same as heuristic | BAJO | Theorem proves equivalence — validates existing code |
| UHF constraint too restrictive | MEDIO | Only advisory (doesn't block E-graph rules) |
| ZK transcript size unknown | BAJO | Parameterize, use concrete STARK examples |

---

## Lecciones Aplicables

| ID | Título | Aplicación |
|----|--------|-----------|
| L-513 | Compositional E2E | fitness = min(components) pattern |
| L-458 | Concrete evalOp | sourceEntropy as concrete function |
| L-550 | 0^0 guard | ilog2 already handles this |
