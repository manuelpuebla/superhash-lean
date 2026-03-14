# SuperHash v2.0

**Diseño autónomo de funciones hash criptográficas via E-graphs + LLM-guided rule discovery + verificación formal en Lean 4.**

## Qué es

SuperHash es un framework verificado formalmente (Lean 4, 0 sorry, 0 custom axioms) que automatiza el diseño de funciones hash criptográficas usando equality saturation sobre E-graphs. Dado un conjunto de reglas de reescritura con pruebas formales de soundness, el sistema:

1. **Satura** un E-graph con diseños hash equivalentes o mejorados
2. **Extrae** una frontera Pareto de diseños óptimos (seguridad × latencia × área)
3. **Certifica** que cada diseño extraído es semánticamente correcto y no-dominado

## Qué resuelve

El diseño de funciones hash es un problema de optimización multi-objetivo donde transformaciones válidas (cambiar S-box, ajustar rondas, modificar capa lineal) preservan o mejoran la seguridad. SuperHash explota esto formalizando cada transformación como una regla de reescritura verificada en Lean 4, y usando E-graphs para explorar exhaustivamente el espacio de diseños equivalentes.

**Pipeline verificado**:
```
CryptoDesign → E-graph saturation → multi-objective extraction → Pareto front certificado
```

## Relevancia

- **Primer framework de síntesis de hash con soundness end-to-end** verificada en un proof assistant
- Construye sobre 5 librerías internas verificadas (~5,669 teoremas totales)
- Patrón transferible: E-graph + verified rules + Pareto extraction aplica a cualquier dominio de diseño

## Stack

- **Lean 4** (sin Mathlib para v1.0)
- **OptiSat** (E-graph engine, ~190 teoremas) — componentes adaptados
- **LeanHash** (~134 teoremas) — espacio de diseño criptográfico adaptado
- **VerifiedExtraction** (~203 teoremas) — estrategia de extracción unificada

## Estructura

```
SuperHash/
├── CryptoOp.lean           -- CryptoConstruction + CryptoOp inductive
├── DesignParams.lean        -- DesignParams, SecurityMetrics, métricas
├── CryptoNodeOps.lean       -- NodeOps typeclass instantiation
├── Pareto.lean              -- Pareto dominance + paretoFront
├── Instances.lean           -- AES-128, Poseidon-128 definitions
├── EGraph/
│   ├── Core.lean            -- EGraph parametric engine
│   ├── UnionFind.lean       -- Union-Find con path compression
│   ├── Consistency.lean     -- ConsistentValuation
│   └── Tests.lean           -- Smoke tests
├── Rules/
│   ├── SoundRule.lean       -- EquivalenceRule + ImprovementRule
│   ├── CryptoRules.lean     -- 5 EquivalenceRules + 5 PatternSoundRules + 3 strategies
│   └── NonVacuity.lean      -- Non-vacuity examples
├── Pipeline/
│   ├── Saturate.lean        -- saturateF (fuel-bounded)
│   ├── ComputeCosts.lean    -- SecurityMetrics annotation
│   ├── Extract.lean         -- CryptoExpr + extractF (greedy)
│   ├── Soundness.lean       -- Stage composition
│   ├── Integration.lean     -- superhash_pipeline
│   └── MasterTheorem.lean   -- pipeline_soundness (3-part)
├── Pareto/
│   ├── Scalarization.lean   -- scalarize + monotonicity
│   ├── Bridge.lean          -- Bool-Prop bridge
│   ├── Extract.lean         -- extractPareto
│   └── Soundness.lean       -- Pareto soundness
└── Instances/
    └── Evaluation.lean      -- #eval concrete instances
Tests/
└── NonVacuity/
    └── Pipeline.lean        -- E2E non-vacuity example
```

## Garantías formales

El teorema maestro `pipeline_soundness` certifica tres propiedades simultáneas:

1. **Semantic correctness**: existe una valuación consistente tal que cada diseño extraído evalúa al valor de la raíz en el grafo saturado
2. **Pareto optimality**: ningún diseño en la salida domina a otro
3. **Output bound**: `output.length ≤ weights.length`

Complementado por `pipeline_metrics_correct`: para cada par `(expr, metrics)` en la salida, `metrics = expr.metrics`.

Axiomas: solo `propext` y `Quot.sound` (kernel de Lean 4). Zero sorry, zero custom axioms.

## v2.0 Roadmap

| Fase | Descripción | Nodos | Estado |
|------|-------------|-------|--------|
| 1 | CryptoOp block constructors + bridge theorems | 7 | Pending |
| 2 | LLM-guided rule discovery + RLVF + AXLE | 8 | Pending |
| 3 | Autonomous design loop + BitVec semantics + SmoothE | 11 | Pending |

Nuevo en v2.0:
- **Block constructors**: spnBlock, feistelBlock, spongeBlock, arxBlock con bridge theorems
- **LLM rule discovery**: CodeEvolve pattern + Lean kernel verification
- **RLVF training**: 4-level rewards (syntax → compile → non-vacuity → Pareto improvement)
- **BitVec concrete semantics**: S-box evaluation via bv_decide (sin Mathlib)
- **SmoothE extraction**: Non-linear Pareto front (non-convex hull)
- **Autonomous loop**: discover → verify → saturate → extract → evaluate → expand

## Estado

v1.0 complete — 27 archivos .lean, ~9000 LOC, 323+ theoremas, 0 sorry, 0 axiomas.
v2.0 planning — 28 nodos, 21 bloques, ~15 archivos Lean nuevos + 6 scripts Python.
Ver [ARCHITECTURE.md](ARCHITECTURE.md).
