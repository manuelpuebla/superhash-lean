# SuperHash — Arquitectura Real, Rol de TrustHash, y Diseño Automático de Ataques

**Fecha**: 2026-03-15
**Proyecto**: SuperHash v3.2

---

## 1. El loop LLM → Lean → E-graph

El flujo es correcto en esencia:

```
LLM propone regla → Lean kernel verifica (PatternSoundRule) → RulePool absorbe
                                                                     ↓
Pareto extrae ← E-graph satura con TODAS las reglas ←──────────────┘
     ↓
Diseños óptimos
```

Lo que el E-graph hace internamente es **agnóstico a la semántica**. `saturateF` aplica rewrite rules y `extractPareto` extrae via scalarización. El master theorem (`pipeline_soundness_crypto`) garantiza que **la semántica se preserva** (CryptoSemantics: 7 campos), no que se optimiza. La optimización viene de la extracción Pareto sobre `SecurityMetrics`.

---

## 2. Tres capas de evaluación de seguridad (NO es solo TrustHash)

La arquitectura tiene **tres capas de evaluación de seguridad**, no una:

### Capa 1: `SecurityMetrics` (durante E-graph extraction)
```lean
-- Pipeline/Integration.lean:37
def superhash_pipeline ... : List (CryptoExpr × SecurityMetrics) :=
  let g_sat := saturateF fuel maxIter rebuildFuel g rules
  extractPareto g_sat weights costFuel rootId
```
`SecurityMetrics` son propiedades **estructurales** del árbol de expresión (profundidad, nodos, etc.). Son lo que Pareto optimiza directamente. **No son métricas de seguridad criptográfica real.**

### Capa 2: `fitness` de CryptoSemantics (evaluación rápida)
```lean
-- Crypto/Fitness.lean:43
def fitness (outputBits sboxBits treewidth : Nat) (cs : CryptoSemantics) : Nat :=
  min birthday (min differential algebraic)
```
Toma CryptoSemantics (7 campos) y computa `min(birthday, differential, algebraic)`. Esta es la fitness **rápida** post-extracción. Es interna a SuperHash, **no viene de TrustHash**.

### Capa 3: `computeFullVerdict` de TrustHash (auditoría profunda)
```lean
-- TrustHash/Verdict.lean:145
def computeFullVerdict (spec : HashSpec) : Verdict :=
  -- 5 dimensiones: generic, differential, algebraic, DP, higher-order
  -- Requiere NiceTree decomposition (precomputada)
```
TrustHash es un **auditor post-hoc**, no la fitness de la saturación. Toma un `HashSpec` completo (incluyendo nice tree decomposition) y produce un veredicto con 5 dimensiones de costo de ataque. **No participa en el loop de saturación.**

### El flujo real es:

```
E-graph saturation (rules)
     ↓
Pareto extraction (SecurityMetrics ← structural)      ← AQUI NO HAY FITNESS CRYPTO
     ↓
CryptoSemantics evaluation (7 campos)                  ← CAPA MEDIA (SuperHash)
     ↓
fitness = min(birthday, diff, algebraic)               ← EVALUACION RAPIDA
     ↓
TrustHash Verdict (5 dimensiones + DP + tree)          ← AUDITORIA PROFUNDA (post-hoc)
```

**La corrección clave**: TrustHash no alimenta la saturación. Es un verificador **downstream**. La fitness durante el design loop (RLVF Level 3) compara Pareto fronts usando `SecurityMetrics`, no TrustHash verdicts. TrustHash entra al cerrar un bloque como auditor.

---

## 3. Papers de UHF y Asymptotic AG: ¿cuánto es realmente TrustHash?

### Carpeta UHF (24 papers)

| Papel | ¿TrustHash o SuperHash? | Justificación |
|-------|------------------------|---------------|
| Carter-Wegman (1979) | **SuperHash** (`UHFConstraint.lean`) | Define familias hash, no analiza ataques |
| Rogaway-Shrimpton (2004) | **SuperHash** (`SecurityNotions.lean`) | Define nociones de seguridad = vocabulario del diseñador |
| Naor-Yung (1991) | **SuperHash** | Composición UOWHF = regla de diseño |
| Charles-Goren-Lauter | **Ambos** | Construcción = SuperHash, reducción a isogenías = TrustHash |
| Rogaway-Steinberger (2008) | **Ambos** | LP family = SuperHash, birthday fraction bounds = TrustHash |
| Hirose DBL (2006) | **SuperHash** | Técnica constructiva |
| Zhupa-Polak (2022) | **Ambos** | Diseño ARX post-quantum = SuperHash, cycle-finding cost = TrustHash |
| Tsurumaru-Hayashi (2012) | **SuperHash** | Dual universality = propiedad de diseño |
| Caillat-Grenier (2024) | **TrustHash** | Spectral gap analysis = técnica de análisis |
| Preneel (1999) | **TrustHash** | Taxonomía de ataques genéricos |
| Al-Kuwari et al. (2011) | **SuperHash** | Multi-property preservation = regla de diseño |
| Tillich-Zémor (2007) | **TrustHash** | Ataque: colisiones LPS |
| Petit (2009, tesis) | **TrustHash** | Atlas de ataques a expander hashes |
| Petit (2009, ZesT) | **Ambos** | Diseño ZesT = SuperHash, análisis resistencia = TrustHash |

**Veredicto UHF**: ~60% SuperHash (diseño), ~40% TrustHash (análisis/ataques), con bastante solapamiento.

### Carpeta Asymptotic AG (16 papers)

| Paper | ¿TrustHash? | Justificación |
|-------|-------------|---------------|
| Feng-Ling-Xing (quantum AG codes) | **Ni SuperHash ni TrustHash actual** | Es fundamento para NUEVOS bounds cuánticos |
| Chang (torres AG) | **Ni** | Maquinaria constructiva para nuevas familias hash |
| Lebacque-Zykin (asymptotics) | **Ni** | Framework teórico fundacional |
| Walsh (polynomial method) | **TrustHash potencial** | Herramientas para probar distribución |
| Inverse sieve (3 papers) | **TrustHash potencial** | Detectar estructura algebraica = análisis |
| Paredes-Sasyk (Hilbert, rational points) | **TrustHash potencial** | Bounds de colisión algebraicos |
| Walsh (multiplicative functions, 3 papers) | **Ninguno** | Muy tangencial |
| Combinatorics, Diff Algebra, Polytopes, Geometry | **Ninguno** | Sin conexión real |

**Veredicto Asymptotic AG**: Solo ~4 papers (inverse sieve + polynomial method) podrían enriquecer TrustHash como verificador. Los 3 papers top (Feng, Chang, Lebacque) son para **extender la maquinaria fundacional**, no para verificación de seguridad. Los 9 restantes no corresponden a ninguno de los dos.

---

## 4. Adaptación para diseño automático de ATAQUES

### La dualidad diseño/ataque

El E-graph engine es **completamente agnóstico**. `saturateF`, `extractPareto`, `pipeline_soundness` trabajan sobre cualquier tipo `Op` y cualquier tipo `Val`. La dualidad es:

| Concepto | Diseño (actual) | Ataque (dual) |
|----------|-----------------|---------------|
| Espacio de búsqueda | `CryptoOp` (12 constructores) | `AttackOp` (nuevos constructores) |
| Semántica | `CryptoSemantics` (7 campos) | `AttackSemantics` (costo, prob, cobertura) |
| Reglas | Equivalencia/mejora de diseños | Composición/extensión de ataques |
| Fitness | **Maximizar** seguridad | **Minimizar** costo de ataque |
| Soundness | "Diseño preserva seguridad" | "Ataque es válido" |
| LLM propone | Reglas de reescritura | Estrategias de ataque |
| Extracción | Diseño Pareto-óptimo | Ataque Pareto-óptimo |

### AttackOp — el tipo dual

```lean
inductive AttackOp where
  -- Differential cryptanalysis
  | diffChar (prob : Nat)              -- differential characteristic
  | truncatedDiff (activeBytes : Nat)  -- truncated differential
  | boomerang (p1 p2 : Nat)           -- boomerang attack
  | impossible (rounds : Nat)          -- impossible differential
  -- Linear cryptanalysis
  | linearTrail (bias : Nat)           -- single linear trail
  | linearHull (numTrails : Nat)       -- hull of correlated trails
  -- Algebraic
  | algebraicRelation (degree : Nat)   -- algebraic equation system
  | grobnerStep                        -- Gröbner basis step
  -- Structural
  | meetInMiddle (splitRound : Nat)    -- MITM
  | zeroSum (degree : Nat)            -- zero-sum distinguisher
  | rebound (inRounds outRounds : Nat) -- rebound attack
  -- Composition (reutiliza el E-graph)
  | compose                            -- sequential composition of attacks
  | parallel                           -- independent parallel paths
  | iterate (rounds : Nat)            -- extend attack across rounds
```

### AttackSemantics — el dominio dual

```lean
structure AttackSemantics where
  timeCost : Nat           -- log2 of time complexity
  memoryCost : Nat         -- log2 of memory required
  dataCost : Nat           -- log2 of chosen/known texts needed
  successProb : Nat        -- -log2 of success probability
  roundsCovered : Nat      -- rounds the attack covers
  attackType : AttackClass -- differential | linear | algebraic | structural
```

### Reglas de reescritura para ataques

```lean
-- Boomerang decomposition: un boomerang ↔ dos truncated differentials
boomerang_decompose : boomerang(p1,p2) ↔ compose(truncatedDiff(p1), truncatedDiff(p2))

-- MITM shift: mover el punto de corte optimiza memoria/tiempo
mitm_shift : meetInMiddle(k) → meetInMiddle(k+1)  -- trades memory for time

-- Impossible extension: agregar ronda a impossible differential
impossible_extend : compose(impossible(r), diffChar(p)) → impossible(r+1)
  -- condición: p > threshold (la extensión es válida)

-- Linear hull aggregation: múltiples trails → hull
linear_aggregate : parallel(linearTrail(b1), linearTrail(b2)) → linearHull(2)

-- Algebraic + differential hybrid
hybrid_attack : compose(diffChar(p), algebraicRelation(d)) → hybridAttack(p, d)
```

### Componentes reutilizables directamente

| Componente SuperHash | Reutilización para ataques |
|---------------------|---------------------------|
| `EGraph/Core.lean` | **100%** — motor idéntico |
| `EGraph/Consistency.lean` | **100%** — ConsistentValuation sobre AttackSemantics |
| `Pipeline/Saturate.lean` | **100%** — `saturateF` es genérico sobre `Op` |
| `Pipeline/Extract.lean` | **100%** — `extractPareto` es genérico |
| `Pipeline/Soundness.lean` | **100%** — composicional sobre cualquier `Val` |
| `Pareto/` | **100%** — dominance, scalarization |
| `Rules/SoundRule.lean` | **95%** — `PatternSoundRule AttackOp AttackSemantics` |
| `Discovery/RuleCandidate.lean` | **80%** — mismo template, distinto payload |
| `Discovery/RulePool.lean` | **80%** — `rulePool_all_sound` sobre AttackOp |
| `DesignLoop/Core.lean` | **70%** — misma estructura, fitness invertida |
| `TrustHash/Verdict.lean` | **Directa** — ya computa costos **desde el atacante** |

Observación clave: **`TrustHash/Verdict.lean` ya es medio motor de ataques**. `differentialCost`, `algebraicCost`, `dpCost`, `higherOrderCost` están computados desde la perspectiva del atacante. Lo que falta es:
1. Hacer esas evaluaciones **composicionales** (combinar ataques parciales)
2. Permitir que el E-graph explore **combinaciones** de técnicas de ataque
3. Invertir la fitness: minimizar costo en vez de maximizar seguridad

### El framework red team + blue team

```
                    ┌──────────────────────┐
                    │   E-Graph Engine     │  ← COMPARTIDO (100%)
                    │  saturateF/extract   │
                    └────────┬─────────────┘
                             │
              ┌──────────────┴──────────────┐
              │                             │
    ┌─────────▼─────────┐       ┌──────────▼──────────┐
    │   BLUE TEAM        │       │   RED TEAM           │
    │   (diseño)         │       │   (ataque)           │
    │                    │       │                      │
    │ CryptoOp           │       │ AttackOp             │
    │ CryptoSemantics    │       │ AttackSemantics      │
    │ max(security)      │       │ min(cost)            │
    │ design rules       │       │ attack composition   │
    │ TrustHash audits   │       │ TrustHash costs      │
    └─────────┬──────────┘       └──────────┬───────────┘
              │                             │
              └──────────────┬──────────────┘
                             │
                    ┌────────▼────────┐
                    │  DUEL THEOREM    │
                    │  security(d) ≥   │
                    │  cost(best_atk)  │
                    └─────────────────┘
```

El **duel theorem** sería el resultado más poderoso: para un diseño `d` extraído por blue team y el mejor ataque `a` encontrado por red team, la seguridad del diseño es al menos el costo del mejor ataque. Si ambos lados saturan completamente, esto es un **bound tight verificado**.

### Papers de Asymptotic AG para ataques (red team)

Los papers que eran tangenciales para diseño se vuelven **centrales** para ataques:

| Paper | Uso en red team |
|-------|----------------|
| Walsh (polynomial method) | Encontrar conjuntos de colisión en variedades algebraicas |
| Inverse sieve (3 papers) | Detectar estructura algebraica explotable en outputs |
| Paredes-Sasyk (rational points) | Bounds sobre puntos en "variedad de colisiones" = costo del ataque |

### Esfuerzo estimado

| Componente | Esfuerzo | Porque |
|-----------|----------|--------|
| `AttackOp` + `AttackSemantics` | BAJO | Definiciones tipo inductive + structure |
| `AttackNodeOps` | BAJO | 4 axiomas, patterns conocidos |
| Attack rewrite rules (10-15) | MEDIO | Cada una requiere prueba de soundness |
| Inversión de fitness | BAJO | Solo cambiar dirección en Pareto |
| Attack composition soundness | ALTO | Probar que la composición de ataques es válida |
| Duel theorem | MUY ALTO | Conectar ambos frameworks formalmente |
| LLM attack proposer | MEDIO | Adaptar `rule_proposer.py` |

**Veredicto**: Una Fase 4 que agregue el red team es **estructuralmente factible** con ~60-70% de reutilización del código existente. El desafío principal es formalizar la **soundness de composición de ataques** (que un boomerang = dos diferenciales truncados, etc.) — es criptografía dura, no ingeniería de software.
