# Insights: SuperHash v4.5.1 Autopsy Fixes — Definitive Resolution

**Fecha**: 2026-03-16
**Dominio**: lean4
**Estado del objeto**: upgrade (corrección post-autopsia)

## 1. Root Cause Analysis

Los 10 issues se agrupan en **3 causas raíz sistémicas**:

### Causa A: Abstraction Mismatch (Issues 1, 5, 6, 7)
`defenseSecurityLevel` usa `computeFullVerdict` (path A: verdict-based).
`designSecurityLevel` usa `evaluateDesign`/`fitness` (path B: fitness-based).
`SecurityMetrics.securityBits` se asigna durante extraction (path C: metrics-based).

Estos 3 paths computan "security" por caminos diferentes y **no están bridgeados**. El issue 1 (tautología) ocurre porque la monotonía evita el path correcto (verdict) y se refugia en birthday binding. El issue 5 (independencia nominal) ocurre porque los "attack models" simplemente re-wrappean el path A. El issue 6 (h_blue restrictivo) ocurre porque el duel exige igualdad entre paths A y B. El issue 7 (métricas desconectadas) ocurre porque path C no tiene bridge con paths A/B.

**Fix sistémico**: Probar bridge theorems entre los 3 paths. Con los bridges, los issues 1, 5, 6, 7 se resuelven como corolarios.

### Causa B: Incomplete Composition (Issues 2, 3, 8)
El pipeline tiene componentes verificados individualmente pero no compuestos end-to-end. Issue 2 (CV sobre graph, no designs) es un gap de composición entre `designLoop_master` y `pipeline_soundness_crypto`. Issue 3 (inductive step sin recursión) es un gap entre el building block y su uso. Issue 8 (h_rules sin discharge) es un gap entre la hipótesis paramétrica y la instanciación concreta.

**Fix sistémico**: Aplicar L-513 (Compositional End-to-End Proofs) para cerrar los 3 gaps con bridges explícitos.

### Causa C: Ornamental Hypotheses (Issues 4, 9, 10)
Issues menores donde hipótesis existen por corrección semántica pero no contribuyen al proof. Issue 4 (h_coverage unused), Issue 9 (hl/hr unused), Issue 10 (all designs same v_sat — correcto pero sutil).

**Fix sistémico**: Fortalecer conclusiones para USAR las hipótesis, o documentar explícitamente como precondiciones de validez.

## 2. Dependency Graph Between Fixes

```
FUNDACIONALES (habilitan otros fixes):
F1: ilog2_mono                    ─── habilita F2
F2: algebraicCost_mono_rounds     ─── habilita F3
F3: verdict_security_mono_rounds  ─── habilita F4, F5

CRÍTICOS:
F4: duel_security_nondecreasing REAL  ◄── F3
F5: pipeline_duel h_blue → ≤       ◄── F3 (relax = a ≤)
F6: designLoop_master Part 4        ◄── patternSoundRules_preserveCV (ya existe)
F7: h_coverage USADO en conclusión

PARALELOS:
F8: dpMultiJoin usa hl/hr          (independiente)
F9: securityBits bridge            (independiente, usa extractPareto internals)
F10: consistent_valuation full      (de-risk, independiente)
```

## 3. Minimal Fix Per Issue

### Issue 1 (CRITICAL): `duel_security_nondecreasing` tautológico

**Root cause**: Hipótesis `h_generic_binding` fuerza birthday-bounded → `x ≤ x`.
**Fix**: Eliminar `h_generic_binding`. Probar monotonía REAL via `differential_mono_rounds` (ya existe) + nuevo `algebraicCost_mono_rounds`. La conclusión verdadera:

```
min(genericFloor, structuralCost spec1) ≤ min(genericFloor, structuralCost spec2)
```

donde `genericFloor` es igual (same outputBits) y `structuralCost` es monotona en rounds (cada componente lo es).

**Prerequisitos**: `ilog2_mono` (nuevo, ~15 LOC), `algebraicCost_mono_rounds` (nuevo, ~25 LOC). `differentialCost` mono ya existe. `dpCost` y `higherOrderCost` mono necesitan proofs (~20 LOC cada uno).

**Riesgo**: `dpCost` usa `securityDP` sobre nice tree — su monotonía en rounds no es directa. Fallback: excluir `dpCost` de la monotonía y agregar hipótesis `dpCost spec1 ≤ dpCost spec2`.

### Issue 2 (HIGH): `designLoop_master` Part 3 sin composición

**Fix**: Agregar Part 4 que compone `∃ v_sat, CV` con `extractPareto_all_correct_cs` para obtener `∀ p ∈ paretoFront, evalExpr p.1 env = v_sat(root)`. Requiere threading `BestNodeInv` y `ExtractableSound` por el loop (ambos preservados por saturateF).

**Prerequisito**: `patternSoundRules_preserveCV` (ya existe en Soundness.lean:56).

### Issue 3 (HIGH): `consistent_valuation_step` sin recursión completa

**Fix**: Probar `AcyclicClassDAG` para e-graphs construidos por `EGraph.empty` + secuencia de `add`. Luego probar el teorema recursivo por inducción bien fundada sobre `rank`.

**Riesgo ALTO**: La acyclicidad post-rebuild es difícil de formalizar (rebuild puede cambiar la estructura del DAG). **Fallback**: Probar solo para e-graphs pre-rebuild (empty + adds, sin merges), que cubre el caso base útil.

### Issue 4 (MEDIUM): `h_coverage` no usado

**Fix**: Cambiar la conclusión de `pipeline_duel` para USAR `h_coverage`. Nueva conclusión: `designSecurityLevel d.1 spec env ≤ a.2.timeCost ∧ a.2.roundsCovered ≥ spec.numRounds`. El `∧` segunda parte viene directamente de `h_coverage`.

### Issue 5 (MEDIUM): Independencia nominal de attack models

**Fix**: Redefinir al menos `algebraicAttackCost` con una formulación genuinamente diferente. Usar Gröbner complexity: `algebraicAttackCost spec = spec.tree.treewidth * (spec.sboxDeg ^ spec.numRounds)` vs. `algebraicCost spec = treewidth * ilog2(iteratedBcd11(...))`. La bridge proof requiere mostrar que Gröbner ≥ BCD11 (que es cierto: BCD11 es un lower bound).

**Riesgo**: La desigualdad Gröbner ≥ BCD11 podría no ser trivial. Fallback: usar `2 * algebraicCost` como upper bound conservativo.

### Issue 6 (MEDIUM): `h_blue` equality demasiado restrictiva

**Fix**: Relajar `h_blue` de `=` a `≤`. Nuevo statement: `designSecurityLevel p.1 spec env ≤ defenseSecurityLevel spec`. La conclusión sigue siendo `designSecurityLevel d.1 spec env ≤ a.2.timeCost` (misma, pero ahora por `≤` transitivo en vez de `=` + `=`). Más diseños satisfacen `≤` que `=`.

### Issue 7 (MEDIUM): `securityBits` desconectado de `evaluateDesign`

**Fix**: Agregar bridge theorem: `∀ p ∈ extractParetoV2 g costs fuel root, p.2.securityBits = evaluateDesign (specToConfig spec) (CryptoExpr.evalCS p.1 env)` (o una versión acotada). Esto requiere entender cómo `extractParetoV2` asigna `securityBits`.

**Alternativa más simple**: Redefinir `bestSecurityBits` sobre `evaluateDesign` directamente en vez de sobre `SecurityMetrics.securityBits`. Esto elimina la necesidad del bridge.

### Issue 8 (MEDIUM): `h_rules` sin discharge

**Fix**: Usar `patternSoundRules_preserveCV` (ya existe) para discharge `PreservesCV` de `cryptoPatternRules`. Para `expansionRules` (que son `RewriteRule`, no `PatternSoundRule`), probar `PreservesCV` individualmente o wrappear como `PatternSoundRule`.

**Alternativa**: Agregar hipótesis que `expansionRules` preservan CV, y discharge solo para `cryptoPatternRules` (que ya está hecho).

### Issue 9 (LOW): `dpMultiJoin_wellformed` params no usados

**Fix**: Reformular `dpMultiJoin` para que USE los inputs wellformed. En vez del dedup guard (que ignora inputs), usar merge-aware insert que combina costs para duplicate keys. O documentar explícitamente que el dedup guard es conservativo y los params son precondiciones de la API.

### Issue 10 (LOW): All designs = same v_sat

**Fix**: Agregar docstring explícito al master theorem explicando que la optimización es sobre COST (latency, gates, etc.), no sobre security level. Todos los diseños son semánticamente equivalentes por construction — esto es una FORTALEZA (soundness), no un bug.

## 4. Key Existing Assets

| Asset | Location | Reusable For |
|-------|----------|-------------|
| `differential_mono_rounds` | Verdict.lean:240 | Issue 1 |
| `sourceEntropy_mono_active` | SourceEntropy.lean | Issue 1 |
| `iterated_bcd11_mono_rounds` | BouraCanteutBound.lean:446 | Issue 1 (algebraicCost) |
| `patternSoundRules_preserveCV` | Soundness.lean:56 | Issues 2, 8 |
| `extractPareto_all_correct_cs` | MasterTheoremCS.lean | Issue 2 |
| `ilog2` definition | AlgebraicDegree.lean:182 | Issue 1 (needs mono proof) |
| `CryptoExpr.metrics` | Pareto/Extract.lean:26 | Issue 7 |
| `toSecurityMetrics` | ExtendedMetrics.lean:45 | Issue 7 |

## 5. Risk Assessment

| Fix | Risk | Fallback |
|-----|------|----------|
| F1 (ilog2_mono) | LOW — pure nat lemma | None needed |
| F2 (algebraicCost_mono) | MEDIUM — depends on ilog2 + if/else | Hypothesis if ilog2 fails |
| F3 (verdict_mono) | MEDIUM — needs all 5 components | Exclude dpCost, add hypothesis |
| F4 (duel_nondecreasing) | LOW once F3 done | — |
| F5 (h_blue relax) | LOW — weaker hypothesis | — |
| F6 (Part 4 composition) | LOW — existing pieces compose | — |
| F7 (h_coverage used) | LOW — trivial conjunction | — |
| F10 (full recursion) | HIGH — acyclicity hard | Pre-rebuild only; or advisory downgrade |

## 6. Recommendations for Planning

1. **DAG order**: F1 → F2 → F3 → {F4, F5} parallel → F6 → F7 → {F8, F9, F10} parallel
2. **De-risk F3 FIRST**: Sketch `verdict_security_mono_rounds` before committing to full plan
3. **Issue 10 is documentation-only**: Don't change code, add docstring
4. **Issue 9 is cosmetic**: Low priority, do last
5. **Issue 3 (HIGH) has HIGH risk**: Plan fallback explicitly in DAG
6. **Total estimated LOC**: ~250-350 new/changed lines
7. **Estimated blocks**: 5-6 blocks in topological order
