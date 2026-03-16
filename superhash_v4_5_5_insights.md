# Insights: SuperHash v4.5.5 — Domain Semantic Bug Fixes

**Fecha**: 2026-03-16
**Dominio**: lean4
**Estado**: bugfix (7 domain-level issues from peer review)

## 1. Issues y Fixes Verificados

### Bug 1 (HIGH): compose.differentialUniformity = max → product

**Archivos**: CryptoEval.lean:113, Instances.lean:244
**Current**: `max f.δ s.δ`
**Fix**: `f.δ * s.δ` (product bound, Lai 1994)
**Impacto**: Dos lugares. No hay teoremas que dependan directamente del valor.

### Bug 2 (HIGH): spnBlock.activeMinSboxes double-count

**Archivos**: CryptoEval.lean:160, Instances.lean:287
**Current**: `r * (mds_branchNumber linearChild.branchNumber) / 2` → aplica t+1 a algo que YA es t+1
**Fix**: `linearChild.branchNumber * (r / 2)` (wide trail: BN × ⌊R/2⌋)
**Impacto**: AES pasa de 30→25. aes128Semantics ya dice 25 (correcto), solo CryptoEval/Instances están mal.

### Bug 3 (MEDIUM): Poseidon δ=2 para campo primo

**Archivos**: Semantics.lean:170, Semantics.lean:196
**Fix**: Documentar limitación. Mantener δ=2 con comment explícito: "Assumed for x^5 over specific ZK primes (BN-254). DDT-based δ over prime fields is prime-dependent, not universally APN."

### Bug 4 (MEDIUM): aes128Semantics.algebraicDegree = 7^10 (loose)

**Archivo**: Semantics.lean:182
**Fix**: Cambiar a 128 (= iteratedBcd11 128 0 4 10, the BCD11 tight bound).
**Verificar**: `#eval iteratedBcd11 128 0 4 10` para confirmar = 128.

### Bug 5 (LOW): degree_upper_bound tautología

**Archivo**: Semantics.lean:214
**Fix**: Eliminar el teorema (no se usa en ningún otro archivo). Reemplazar con el bound real:
`theorem degree_upper_bound_real (n : Nat) (hn : n ≥ 1) : n - 1 ≤ 2^n - 2` (provable por omega).

### Bug 6 (LOW): sponge δ = min(δ, 2^cap) sin documentar

**Archivos**: CryptoEval.lean:179-183, Instances.lean:301-306
**Fix**: Agregar comment "Single-query bound. For q queries: min(δ, q²/2^c) (Bertoni et al. 2008)."

### Bug 7 (LOW): bridge_collision_le_* misleading name

**Archivo**: SecurityNotions.lean:375-393
**Fix**: Actualizar docstrings. Renombrar a `bound_collision_by_*` para evitar implicar reducción adversarial.

## 2. Dependencias entre Fixes

```
Independientes (todos paralelos):
  Bug 1 (compose δ)
  Bug 2 (activeMinSboxes)
  Bug 3 (Poseidon comment)
  Bug 4 (AES degree)
  Bug 5 (delete tautology)
  Bug 6 (sponge comment)
  Bug 7 (rename bridges)
```

Ningún fix depende de otro. Todos son paralelos.

## 3. Archivos Impactados

| Archivo | Bugs | Cambio |
|---------|------|--------|
| `Crypto/CryptoEval.lean` | 1, 2, 6 | Fix fórmulas compose + spnBlock + sponge comment |
| `Pipeline/Instances.lean` | 1, 2, 6 | Same fixes en evalCS |
| `Crypto/Semantics.lean` | 3, 4, 5 | Fix Poseidon/AES values + delete tautology |
| `Crypto/SecurityNotions.lean` | 7 | Rename + docstring |

## 4. Cascading Effects

- **Bug 1** (compose δ product): `defenseSecurityLevel` y `evaluateDesign` producirán valores MENORES (tighter bound). Los non-vacuity examples con `matchingSemantics` en DuelTheorem.lean pueden necesitar recalibración.
- **Bug 2** (activeMinSboxes): Los `#eval` smoke tests en CryptoEval.lean producirán valores diferentes.
- **Bug 4** (AES degree 128 vs 7^10): `evaluateDesign aes128Config aes128Semantics` cambiará de 64 a un valor diferente (el fitness usa `ilog2(algebraicDegree)`, y `ilog2(128) = 7` vs `ilog2(7^10) = 28`).

## 5. Estimación

~60-80 LOC de cambios. 0 archivos nuevos. Build debe pasar sin sorry.
