# Insights: SuperHash v2.7 — Sorry Closure + AES DDT + CryptoSemantics Pipeline

**Fecha**: 2026-03-14
**Dominio**: lean4
**Estado del objeto**: upgrade (v2.6 complete, 3 tasks pending)

---

## 1. Análisis del Objeto de Estudio

### Tres tareas para v2.7

| Task | Descripción | Dificultad | Archivos |
|------|-------------|-----------|----------|
| T1 | Cerrar 2 sorry (pool preservation + list length) | BAJA | MasterTheoremV2.lean, SmoothE/Extract.lean |
| T2 | AES S-box DDT certificada (256 entradas, δ=4) | BAJA | Crypto/DDT.lean (nuevo: AESSbox.lean) |
| T3 | Pipeline `pipeline_soundness` sobre CryptoSemantics | ALTA | Crypto/NodeSemInstance.lean + pipeline chain |

---

## 2. Hallazgos Clave

### Hallazgo 1: TrustHash YA tiene la tabla AES S-box

**Archivo**: `~/Documents/claudio/TrustHash/TrustHash/Sbox/AES8BitSbox.lean` (líneas 37-86)

La tabla completa de 256 entradas está definida como `aesSboxTable : Array Nat` con verificación `aesSboxTable_size : aesSboxTable.size = 256 := by native_decide`. El wrapper `aesSbox8 : ConcreteSbox` también existe.

**Nota crítica**: El comentario en líneas 4-20 advierte que `native_decide` sobre `diffUniformityFromTable` para 256 entradas **fue demasiado lento**. TrustHash usa un patrón de certificado en su lugar.

**Impacto**: Copiar la tabla de TrustHash, pero NO intentar `native_decide` sobre el DDT completo. Usar el patrón de certificado de TrustHash o factorizar la verificación.

### Hallazgo 2: `List.length_filterMap_le` EXISTE en Init

**Disponible en Lean 4.28.0 Init.Data.List.Lemmas** (sin Mathlib):
- `List.length_filterMap_le : (List.filterMap f l).length ≤ l.length`
- `List.length_filter_le : (List.filter p l).length ≤ l.length`

Esto resuelve 2 de los 3 pasos del sorry de `extractParetoV2_length_le`. El paso restante (foldl dedup ≤ input) necesita un lema custom.

### Hallazgo 3: Patrón exacto para sorry de designLoop

El proof de `designLoop_fuel_zero` (Core.lean:107-117) es el patrón a seguir:
```lean
theorem designLoop_fuel_zero (state : DesignLoopState) :
    (designLoop state).fuel = 0 := by
  unfold designLoop
  split
  · next h => exact h
  · apply designLoop_fuel_zero
termination_by state.fuel
decreasing_by
  simp_wf
  have h := designLoopStep_fuel_decreasing state (by omega)
  exact h
```

Para pool preservation, reemplazar `.fuel = 0` por `.pool = state.pool` y usar `designLoopStep_preserves_pool` (que es `rfl` por struct update) en el paso inductivo.

### Hallazgo 4: native_decide timeout para 256 entradas

Issue #3935 de Lean 4: pattern matching sobre Nat con ~300+ cases causa timeout. Para la DDT de AES (256×256 = 65K comparaciones sobre `List.range 256`):
- `native_decide` debería funcionar porque usa código nativo compilado (no kernel reduction)
- Pero si falla, usar `#eval` como oráculo + axiom documentado
- TrustHash ya solucionó esto con patrón de certificado (no `native_decide` directo)

### Hallazgo 5: NodeSemantics es parametric — instanciación debería propagar

Los ~200 theorems del E-graph core (Consistency.lean, CoreSpec.lean) están parametrizados por `[NodeSemantics Op Val]`. En principio, al definir `instance : NodeSemantics CryptoOp CryptoSemantics`, TODOS los teoremas se instancian automáticamente.

**PERO**: Los proofs de `evalOp_ext`, `evalOp_mapChildren`, `evalOp_skeleton` (Tests.lean:53-113) hacen `cases op` para 12 constructores. Con CryptoSemantics, estos proofs se re-usan pero las evaluaciones de `evalCryptoSem` (CryptoEval.lean) producen `CryptoSemantics` en vez de `Nat`. Las tácticas `simp` + `omega` que cierran los goals Nat pueden fallar para goals CryptoSemantics (struct equality).

**Solución**: Usar `decide` o `native_decide` para struct equality goals, o `ext` + `simp` para descomponer la igualdad campo a campo.

---

## 3. Lecciones Aplicables

| ID | Título | Aplicación |
|----|--------|-----------|
| L-643 | AllNonRecursive composition | Patrón para pool preservation inductiva |
| L-284 | Lexicographic termination_by | Fuel-based loop con structural recursion |
| L-371 | FoldMin theorems (DynamicTreeProg) | Copy-adapt foldl bounds |
| L-458 | Concrete evalOp vs typeclass | CryptoSemantics: concrete, no typeclass overhead |
| L-566 | Bool-to-Prop bridge | native_decide para AES DDT |
| L-567 | native_decide performance | Timeout risk para 256-element S-box |
| L-652 | WF recursion equation lemmas | generalize+cases para evitar kernel unfolding |

### Anti-patrones
- **NO** intentar `native_decide` sobre DDT completo de AES sin fallback (L-567)
- **NO** forzar NodeSemantics Option-returning (L-465) — usar concrete evalOp
- **NO** definir AES S-box con 256-case `match` — usar Array literal (Issue #3935)

---

## 4. Código Reutilizable de Librerías

### De TrustHash (copiar)
| Archivo | Contenido | Uso |
|---------|-----------|-----|
| `Sbox/AES8BitSbox.lean:37-86` | Tabla AES S-box 256 entradas | Copiar directamente para T2 |
| `Sbox/AES8BitSbox.lean:89-100` | Size proof + ConcreteSbox wrapper | Adaptar a SuperHash ConcreteSbox |

### De OptiSat (pattern)
| Archivo | Contenido | Uso |
|---------|-----------|-----|
| `Util/FoldMin.lean:14-80` | 6 theorems foldl_min_* | Pattern para foldl bounds en T1 |
| `SaturationSpec.lean:84-268` | Preservation proofs (AddExprInv, CV) | Pattern para T3 preservation chain |
| `ILPSpec.lean:67-80` | `foldl_bool_true` helper | Pattern para dedup bound en T1 |

### De VerifiedExtraction (pattern)
| Archivo | Contenido | Uso |
|---------|-----------|-----|
| `Greedy.lean:57-64` | `mapOption_length` (length preservation) | Pattern para filterMap bound en T1 |

### De Lean 4 Init (usar directamente)
| Lema | Signature | Uso |
|------|-----------|-----|
| `List.length_filterMap_le` | `(filterMap f l).length ≤ l.length` | T1 sorry paso 1 |
| `List.length_filter_le` | `(filter p l).length ≤ l.length` | T1 sorry paso 3 |

---

## 5. Estrategias de Resolución

### T1a: designLoop_preserves_pool

**Estrategia**: Mirror de `designLoop_fuel_zero` proof (ya funciona):
```lean
theorem designLoop_preserves_pool (state : DesignLoopState) :
    (designLoop state).pool = state.pool := by
  unfold designLoop
  split
  · rfl  -- fuel = 0: designLoop returns state unchanged
  · -- fuel > 0: step preserves pool, then IH
    simp only [designLoopStep_preserves_pool]
    exact designLoop_preserves_pool _
termination_by state.fuel
decreasing_by
  simp_wf
  exact designLoopStep_fuel_decreasing state (by omega)
```

**Riesgo**: El `simp only [designLoopStep_preserves_pool]` puede no simplificar directamente dentro del `let`. Alternativa: `show (designLoop (designLoopStep state)).pool = state.pool` → `rw [designLoop_preserves_pool, designLoopStep_preserves_pool]`.

### T1b: extractParetoV2_length_le

**Estrategia de 3 pasos**:
1. `List.length_filterMap_le` — candidates ≤ suite (disponible en Init)
2. Lema custom: foldl dedup ≤ input — probar que `foldl (if dup skip else cons) [] l` tiene length ≤ l.length por inducción
3. `List.length_filter_le` — filter ≤ deduped (disponible en Init)
4. Componer con `Nat.le_trans`

**Dificultad del paso 2**: El foldl acumula en un `acc : List _` que crece. Necesitamos probar que `acc.length + remaining.length ≤ original.length` como invariante del loop. Alternativa: probar que el resultado de foldl tiene length ≤ input.length directamente por inducción sobre la lista input.

### T2: AES S-box DDT

**Estrategia**:
1. Copiar `aesSboxTable` de TrustHash/Sbox/AES8BitSbox.lean
2. Crear `aesSbox : ConcreteSbox` con `bits := 8, table := aesSboxTable, h_size := by native_decide`
3. Intentar `aesCertified : CertifiedSbox` con `h_delta := by native_decide`
4. **Fallback** si native_decide timeout: usar `#eval diffUniformity aesSbox` para verificar = 4, luego `h_delta := by native_decide` con `set_option maxHeartbeats 4000000`
5. **Fallback 2**: Si sigue lento, usar patrón de TrustHash (certificado pre-computado)

### T3: NodeSemantics CryptoSemantics

**Estrategia incremental**:
1. Definir `evalCryptoOpCS` como `evalCryptoSem` pero con firma compatible con NodeSemantics
2. Probar `evalOp_ext_cs`, `evalOp_mapChildren_cs`, `evalOp_skeleton_cs` — misma estructura que Tests.lean proofs pero con CryptoSemantics goals
3. Crear `instance : NodeSemantics CryptoOp CryptoSemantics`
4. Verificar que `ConsistentValuation (g : EGraph CryptoOp) (env : Nat → CryptoSemantics) (v : EClassId → CryptoSemantics)` compila
5. Los ~200 theorems deberían instanciarse automáticamente via el typeclass
6. Crear `pipeline_soundness_crypto` composicionalmente

**Obstáculo principal**: `evalOp_skeleton_cs` proof genera 12×12 = 144 subgoals (vs 8×8 = 64 en Nat). Cada subgoal necesita `CryptoSemantics` equality, que requiere `ext` para descomponer en 7 campo. Usar `all_goals (first | ... | ext <;> simp ...)`.

---

## 6. Síntesis

### Top 5 Insights

1. **TrustHash tiene la tabla AES** — no necesitamos escribirla, solo copiar
2. **`List.length_filterMap_le` está en Init** — 2/3 del sorry de extractPareto se cierra gratis
3. **`designLoop_preserves_pool` sigue el patrón exacto de `designLoop_fuel_zero`** — mirror proof
4. **native_decide puede fallar para 256-entry DDT** — tener fallback ready (heartbeats o certificado)
5. **NodeSemantics es parametric** — instanciar CryptoSemantics propaga ~200 theorems automáticamente

### Riesgos

| Riesgo | Nivel | Mitigación |
|--------|-------|-----------|
| native_decide timeout AES DDT | MEDIO | Heartbeats ↑ o certificado TrustHash pattern |
| foldl dedup length bound | BAJO | Custom induction lemma (5-10 líneas) |
| evalOp_skeleton 144 subgoals | MEDIO | `all_goals` con `ext <;> simp` combinator |
| CryptoSemantics equality in simp | BAJO | `decide` o `native_decide` para struct eq |

### Recomendación

Ejecutar en orden: T1a (5 min) → T1b (15 min) → T2 (30 min) → T3 (2-4 horas).
Total estimado: medio día de trabajo.
