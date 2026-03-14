# SuperHash: Diseño Automático de Funciones Hash via E-graphs + LLMs + Verificación Formal

> Documento generado a partir de sesión de diseño sobre TrustHash (v3.1.1), marzo 2026.

---

## Contexto: TrustHash como base

TrustHash es una biblioteca de verificación formal (Lean 4, 2,219 teoremas, 0 sorry) que analiza la seguridad de funciones hash. El modelo central:

```
security_level = min(generic_floor, structural_cost)
```

Pipeline verificado completo:
```
S-box table → AutoSboxPipeline → SboxCertifiedParams →
  HashExprF → E-graph saturation (12 reglas) →
    Constraint graph → Tree decomposition →
      Nice tree → Security DP (con prueba de optimalidad) → Veredicto
```

**El cambio de paradigma**: pasar de ANÁLISIS (evaluar un hash dado) a SÍNTESIS (diseñar un hash óptimo).

---

## E-graphs: de analizador a explorador de diseños

Hoy en TrustHash, el E-graph hace esto:

```
HashExprF (fija) → saturation (12 reglas) → expresión equivalente más simple → medir profundidad
```

Pero la estructura del E-graph tiene una propiedad fundamental que no estamos explotando: **representa exponencialmente muchos programas equivalentes en espacio polinomial**. Equality saturation explora **todos los caminos de reescritura simultáneamente**.

El cambio de paradigma:

```
HOY:     una expresión hash → simplificar → medir
FUTURO:  un espacio de diseños hash → saturar → extraer el óptimo
```

---

## El E-graph como explorador del espacio de diseño

### Paso 1 — Elevar el lenguaje de términos

Hoy `HashExprF` modela operaciones dentro de un hash (Sbox, ARK, Comp). Para diseño, necesitamos un lenguaje que modele **construcciones completas**:

```
CryptoDesign :=
  | SPN (sbox : SboxSpec) (linear : LinearSpec) (rounds : Nat)
  | Feistel (f : RoundFn) (rounds : Nat)
  | Sponge (perm : PermSpec) (rate capacity : Nat)
  | Compose (d1 d2 : CryptoDesign)        -- composición secuencial
  | Parallel (d1 d2 : CryptoDesign)       -- ejecución paralela
  | Iterate (d : CryptoDesign) (n : Nat)  -- repetición
```

Cada nodo del E-graph es un diseño completo o parcial. Dos nodos en la misma e-class son **diseños equivalentes en seguridad** (probado).

### Paso 2 — Reglas de reescritura como transformaciones de diseño

Cada regla transforma un diseño válido en otro equivalente o mejor, con prueba formal:

```
-- Composición de rondas (verificado: seguridad se preserva)
SPN(s, l, r₁) ∘ SPN(s, l, r₂)  ⟹  SPN(s, l, r₁ + r₂)

-- Sustitución de S-box por una con menor δ (mejora diferencial)
SPN(s₁, l, r)  ⟹  SPN(s₂, l, r)    si δ(s₂) < δ(s₁) ∧ deg(s₂) ≥ deg(s₁)

-- Reducción de rondas si la seguridad sigue siendo suficiente
SPN(s, l, r)  ⟹  SPN(s, l, r-1)     si structural_cost(s, l, r-1) ≥ target

-- Cambio de construcción (Feistel ↔ SPN con seguridad comparable)
Feistel(f, 3r)  ⟹  SPN(s, l, r)     si security_equiv(...)

-- Luby-Rackoff: 3 rondas Feistel → PRP
Feistel(f, r)  ⟹  PRP(f)            si r ≥ 3

-- Wide trail: sustituir linear layer por MDS con mayor branch number
SPN(s, l₁, r)  ⟹  SPN(s, l₂, r')   si bn(l₂) > bn(l₁) ∧ r' < r ∧ security preservada
```

**Cada regla tiene una prueba de soundness en Lean.** No se puede introducir una transformación incorrecta.

### Paso 3 — Saturación = exploración exhaustiva

Equality saturation aplica **todas las reglas a todos los nodos** hasta un punto fijo. Partiendo de un diseño inicial (e.g., AES-128), el E-graph genera automáticamente:

```
e-class₁ = { AES-128,
              SPN(aes_sbox, aes_mds, 10),
              SPN(aes_sbox, aes_mds, 9) ∘ AddKey,    -- descompuesto
              SPN(better_sbox, aes_mds, 10),          -- S-box mejorada
              SPN(aes_sbox, better_mds, 8),           -- mejor MDS, menos rondas
              ... cientos de variantes equivalentes }
```

Todo en espacio polinomial. Todas verificadamente equivalentes en seguridad o mejores.

### Paso 4 — Extracción multi-objetivo

TrustHash ya tiene extracción cost-guided (greedy + ILP). Hay que extenderla a multi-objetivo:

```
cost(design) = (1/security(design),  latency(design),  area(design))
                ────────────────     ──────────────     ────────────
                minimizar            minimizar          minimizar
```

La extracción produce la **frontera Pareto**: todos los diseños no-dominados.

```
        security ↑
             │  ★ SHA-3-256 (seguro pero lento)
             │    ★ Diseño nuevo A (igual seguridad, más rápido)
             │       ★ Diseño nuevo B
             │          ★ AES-128
             │              ★ Diseño nuevo C (rápido, seguridad suficiente)
             └──────────────────────────→ performance
```

---

## E-graphs vs LLMs: comparación directa

| Dimensión | E-graphs | LLMs |
|-----------|----------|------|
| **Exploración** | Exhaustiva dentro del rule set | Sampling heurístico |
| **Soundness** | Garantizada (cada regla probada) | Ninguna (puede inventar basura) |
| **Completitud** | Completa para reglas dadas | Incompleta pero puede saltar lejos |
| **Creatividad** | Nula — solo aplica reglas conocidas | Alta — puede proponer lo inesperado |
| **Reproducibilidad** | Determinista | Estocástica |
| **Optimalidad** | Óptima para la cost function dada | Sin garantía |
| **Escalabilidad** | Polinomial en reglas/términos | Escala con GPU y datos |
| **Aprendizaje** | No aprende | Generaliza de ejemplos |

**Conclusión**: no son alternativas, son **complementarios**. Cubren debilidades opuestas.

---

## La arquitectura combinada: LLM × E-graph × TrustHash

```
┌─────────────────────────────────────────────────────────┐
│                    LOOP PRINCIPAL                         │
│                                                          │
│  ┌──────────┐   propone reglas    ┌────────────────┐    │
│  │          │ ──────────────────→ │                │    │
│  │   LLM    │                     │   TrustHash    │    │
│  │ (creative│ ←────────────────── │   (verifier)   │    │
│  │  engine) │   sound? sí/no      │                │    │
│  └──────────┘                     └───────┬────────┘    │
│       │                                   │             │
│       │ reglas verificadas                │             │
│       ▼                                   │             │
│  ┌──────────────────┐                     │             │
│  │                  │   cost function     │             │
│  │  E-graph engine  │ ←──────────────────┘             │
│  │  (exhaustive     │                                   │
│  │   explorer)      │                                   │
│  │                  │                                   │
│  └────────┬─────────┘                                   │
│           │                                              │
│           │ frontera Pareto de diseños                   │
│           ▼                                              │
│  ┌──────────────────┐                                   │
│  │  Extraction       │──→ mejores diseños verificados   │
│  │  (ILP/greedy)     │                                   │
│  └──────────────────┘                                   │
└─────────────────────────────────────────────────────────┘
```

### El rol de cada componente

**LLM — Motor creativo** (propone, no decide):
- Genera candidatos de reglas de reescritura: "para esta S-box específica, `sbox(sbox(x)) = linear(x) + c`"
- Propone construcciones novedosas: "¿qué pasa si combinamos Feistel con S-box parcial?"
- Sugiere S-boxes con propiedades deseadas
- Genera hipótesis algebraicas sobre familias de diseños

**TrustHash — Verificador** (filtra, certifica):
- Verifica cada regla propuesta por el LLM → acepta o rechaza con contraprueba
- Evalúa cada diseño extraído → security score certificado
- Produce proof certificates para cada paso
- Garantiza que **nada incorrecto entra al E-graph**

**E-graph — Explorador exhaustivo** (optimiza, combina):
- Absorbe las reglas verificadas
- Satura: explora TODAS las combinaciones de reglas
- Encuentra diseños que ningún componente individual descubriría
- Extracción produce el óptimo global (no local)

### Por qué la combinación es más que la suma

Ejemplo concreto:

1. **LLM propone** (creativo pero no sound):
   - Regla A: "S-box de Poseidon al cubo es equivalente a identidad en GF(p)" → TrustHash rechaza (falso)
   - Regla B: "Para alpha=5, `sbox^5(x) = x` en GF(p)" → TrustHash verifica: **sound**
   - Regla C: "MDS Cauchy con estos parámetros tiene branch number 5" → TrustHash verifica: **sound**

2. **E-graph absorbe** B y C (solo las verificadas):
   - Satura partiendo de Poseidon-128
   - Descubre: "con regla B, el grado algebraico después de 3 rondas full + 1 partial es suficiente para seguridad 64-bit, y con regla C el branch number permite reducir de 8 a 6 rondas full"
   - Este diseño **no fue propuesto por el LLM ni por el E-graph individualmente** — emergió de la combinación de reglas verificadas durante saturación

3. **Extracción** produce: Poseidon variante con 6 rondas full (vs 8 original), misma seguridad, 25% más rápido

Ningún componente solo podría lograr esto:
- El LLM no sabe explorar exhaustivamente
- El E-graph no puede inventar la regla B
- TrustHash no busca, solo verifica

---

## Esquema de trabajo: el agente diseñador (sin E-graphs)

### Capa 1 — Espacio de búsqueda parametrizado

```
HashDesign = {
  construction : SPN | Feistel | Sponge | ARX
  sbox_table   : Array (Fin 2^k) (Fin 2^k)
  linear_layer : Matrix n n (GF 2^k)
  rounds_full  : Nat
  rounds_partial : Nat
  state_width  : Nat
  output_bits  : Nat
}
```

### Capa 2 — Evaluación multi-objetivo

| Objetivo | Fuente | Verificable formalmente |
|----------|--------|------------------------|
| Seguridad diferencial (δ^active_sboxes) | TrustHash DP | Sí |
| Seguridad algebraica (d^treewidth) | TrustHash E-graph + DP | Sí |
| Piso genérico (birthday, GBP, Joux) | TrustHash GenericFloor | Sí |
| Latencia (ciclos por byte) | Modelo de performance | Parcialmente |
| Throughput (GB/s) | Benchmark o modelo | No (empírico) |
| Eficiencia en hardware (gates, area) | Modelo de circuito | Parcialmente |
| Resistencia a side-channels | Análisis de potencia/timing | No |

### Capa 3 — Estrategias de búsqueda

- **Evolutionary**: población de diseños, crossover de S-boxes y parámetros, mutación. TrustHash como fitness.
- **Bayesian optimization**: modelo surrogate de la función security(params), acquisition function para decidir qué evaluar.
- **Monte Carlo Tree Search**: explorar el árbol de decisiones (primero construction, luego S-box, luego linear layer, luego rounds).

---

## Integración con LLMs: RLVF

### Arquitectura A — RLVF (Reinforcement Learning from Verified Feedback)

```
┌─────────────┐     propone diseño      ┌──────────────┐
│             │ ──────────────────────→  │              │
│   LLM       │                          │  TrustHash   │
│  (policy)   │  ←──────────────────── │  (verifier)  │
│             │    reward = f(security,  │              │
└─────────────┘    performance, proof)   └──────────────┘
       ↑                                        │
       │         gradient update                │
       └────────────────────────────────────────┘
```

**Cómo funciona:**
1. El LLM genera un `HashSpec` en Lean 4 (o un vector de parámetros)
2. TrustHash evalúa y produce: veredicto + proof certificate
3. El reward es: `r = α·security_level + β·(1/latency) + γ·proof_completeness`
4. Se actualiza la policy del LLM via PPO/DPO

**Analogía**: AlphaProof (DeepMind) usa un loop similar — LLM propone pasos de prueba, Lean verifica, la señal de verificación entrena al modelo.

### Arquitectura B — Neuro-symbolic con E-graphs

El LLM propone **reglas de reescritura** para el E-graph:

```
LLM propone: "sbox(sbox(x)) puede simplificarse a linear(x) + c para esta S-box"
TrustHash:    verifica la regla → si es sound, la agrega al E-graph
              re-satura → obtiene nueva profundidad/treewidth
              evalúa impacto en seguridad
```

### Arquitectura C — Entrenamiento end-to-end

El LLM genera directamente archivos `.lean` con diseños + pruebas:

```
Training objective = maximize P(lean_file compiles ∧ security ≥ target ∧ performance ≥ baseline)
```

---

## Qué es reutilizable de TrustHash

| Componente TrustHash | Uso en arquitectura combinada | Status |
|-----------------------|-------------------------------|--------|
| Pipeline como fitness | Cost function del E-graph | **Directo** — ya existe |
| 12 reglas de reescritura con soundness | Reglas iniciales del E-graph | **Directo** — ya verificadas |
| E-graph core (20 files, 300 thms) | Motor de saturación | **Directo** — ya funciona |
| ILP extraction | Extracción multi-objetivo | **Extender** — agregar Pareto |
| S-box certified pipeline | Verificación de S-boxes propuestas | **Directo** — ya funciona |
| DP over nice trees | Evaluación de seguridad de diseños extraídos | **Directo** — ya funciona |
| RLVF loop | LLM → verificar → entrenar | **Nuevo** — LLM propone reglas, no diseños |
| Espacio parametrizado | Tipo `CryptoDesign` para el E-graph | **Adaptar** — elevar a lenguaje de diseño |
| Performance model | Segundo eje de la cost function | **Nuevo** — hay que implementar |
| Non-vacuity framework | Validar que las reglas no son vacuas | **Directo** — ya existe |

---

## Autonomía: qué puede ser autónomo y qué no

### Puede ser autónomo

1. **Búsqueda de S-boxes óptimas**: espacio finito, evaluación formal, criterios precisos.
2. **Optimización de rondas**: búsqueda lineal con evaluación formal.
3. **Exploración de la frontera Pareto**: generar, evaluar, extraer. Paralelizable.
4. **Descubrimiento de reglas de reescritura**: LLM propone, TrustHash verifica. Loop seguro.
5. **Saturación y extracción**: completamente determinista y verificado.

### Requiere intervención humana

| Ataque | Modelado por TrustHash | En la realidad |
|--------|----------------------|----------------|
| Diferencial | Sí (δ^active_sboxes) | Más complejo (trails, probabilidades, clustering) |
| Algebraico | Sí (d^treewidth) | Más complejo (Gröbner bases, SAT solvers) |
| Lineal | Parcialmente (LAT, Matsui) | Más complejo (linear hulls, multidimensional) |
| Birthday/GBP/Joux | Sí | Completo para estos ataques |
| Slide attacks | No | Relevante para diseños con simetría |
| Related-key | No | Relevante para block ciphers como hash |
| Side-channel | No | Irreducible a análisis estático |
| Quantum (Grover/Simon) | No | Reducción cuadrática de búsqueda |
| Invariant subspace | No | Rompió Midori, Prince |
| Integral/higher-order diff | No | Relevante para pocas rondas |

**Un hash que TrustHash certifica como "optimal" podría ser inseguro contra un ataque no modelado.** Un criptógrafo humano debe validar el diseño final.

### El esquema autónomo seguro

```
Autónomo:     LLM propone reglas → TrustHash verifica → E-graph satura → extrae óptimo
                                                                          ↓
                                                          Candidato "óptimo dentro del modelo"
                                                                          ↓
Humano:                                                   Revisión por criptógrafo experto
                                                          (ataques no modelados, side channels,
                                                           quantum, implementación)
```

---

## Plan de implementación

### Fase 1 — E-graph de diseños (construye sobre lo existente)

```
Nuevo:   CryptoDesign.lean     -- tipo de términos de diseño
Nuevo:   DesignRules.lean      -- 20-30 reglas de diseño verificadas
Adaptar: EGraph/Core.lean      -- parametrizar sobre CryptoDesign
Adaptar: EGraph/Extraction     -- multi-objetivo Pareto
Existe:  EGraph/Saturate       -- reutilizar directamente
Existe:  Pipeline/             -- cost function
```

### Fase 2 — Rule discovery loop

```
Nuevo:   RuleProposer.lean     -- interface para reglas candidatas
Nuevo:   RuleVerifier.lean     -- verifica soundness automáticamente
Nuevo:   rule_discovery.py     -- LLM propone → Lean verifica → E-graph absorbe
Existe:  HashSoundRules.lean   -- framework de soundness proofs
```

### Fase 3 — Autonomous design loop

```
Nuevo:   DesignLoop.lean       -- loop: saturate → extract → evaluate → expand rules
Nuevo:   ParetoTracker.lean    -- mantener frontera Pareto actualizada
Nuevo:   design_agent.py       -- orquestador Python: LLM + Lean + E-graph
Existe:  Todo TrustHash        -- evaluación verificada
```

---

## El insight central

El diseño de funciones hash es fundamentalmente un problema de **equivalencia algebraica + optimización**:

- Dos hash con diferente estructura pueden tener la misma seguridad
- Queremos encontrar el más eficiente entre los equivalentemente seguros
- Las transformaciones válidas son algebraicas
- La optimalidad es respecto a una función de costo multi-dimensional

Esto es **exactamente** para lo que se inventaron los E-graphs (egg, Willsey et al. 2021): "equality saturation finds optimal programs by exploring the space of equivalent programs and extracting the best one."

Un LLM haciendo sampling en el espacio de diseños es como buscar una aguja en un pajar con una linterna. Un E-graph con reglas verificadas es como tener un mapa del pajar completo y caminar directamente a la aguja.

**La combinación LLM + E-graph + TrustHash es estrictamente más poderosa que cualquier componente individual.** El LLM aporta creatividad, el E-graph aporta exhaustividad, TrustHash aporta corrección.

---

## Limitaciones conocidas de TrustHash (para contexto)

1. **Treewidth heurístico**: greedy min-degree elimination (upper bound, no exacto para grafos arbitrarios)
2. **Extracción E-graph greedy**: ILP encoding existe pero solver es externo
3. **Costos abstractos**: unidades de costo, no bits de seguridad directamente
4. **DP exponencial con fuel**: cae a lineal cuando se agota
5. **Sin key schedules completos**: solo funciones de ronda
6. **Rondas independientes**: no modela ataques correlacionados
7. **Sin Mathlib**: Nat-based, no GF(2^n) formal ni probabilidad measure-theoretic

Estas limitaciones se asumen resueltas en el "trabajo futuro completado" que es prerrequisito de este documento.
