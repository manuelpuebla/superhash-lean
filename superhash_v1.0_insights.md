# Insights: Diseño Automático de Funciones Hash Criptográficas via E-graphs + LLMs + Verificación Formal

**Fecha**: 2026-03-13
**Dominio**: lean4
**Estado del objeto**: upgrade (construye sobre TrustHash v4.0.3 — 2,160 teoremas, 190 archivos, 0 sorry)
**Proyecto destino**: SuperHash (Lean 4.28 con Mathlib)
**Librería de formalización**: LeanHash (~146 teoremas, Lean 4.16.0)

---

## 1. Análisis del Objeto de Estudio

### Resumen

SuperHash integra **síntesis automática de funciones hash criptográficas** con tres pilares: (1) **e-graphs para exploración exhaustiva** de diseños equivalentes via equality saturation y reescritura verificada, (2) **LLMs para creatividad** en propuesta de reglas de reescritura y configuraciones, y (3) **TrustHash como evaluador formal** de seguridad basado en modelo de dos capas (piso genérico + costo estructural). El proyecto cierra el ciclo análisis→síntesis integrando herramientas emergentes: AXLE (verificación rápida), AlphaEvolve/OpenEvolve (evolución con LLMs), y SSD (meta-predicción de verificación).

### Keywords

equality saturation, e-graphs, sound rewrite rules, CryptoDesign, RLVF, Pareto extraction, treewidth DP, AXLE, AlphaEvolve, SSD, generic_floor, structural_cost, verified loop, neuro-symbolic, AutoSboxPipeline

### Estado Actual

- **superhash_idea.md**: Borrador conceptual (421 líneas), visión de 3 fases, CryptoDesign type, RLVF loop
- **TrustHash v4.0.3**: Release estable — 2,160 teoremas, 190 archivos, pipeline de análisis completo con 6 instancias de hash, v4.0 con ataques expandidos (Division Property, Quantum, Slide, Related-Key, Invariant Subspace, Side-Channel)
- **LeanHash**: 134 teoremas base (Birthday, GBP, Joux, S-box, MDS, DiffPath, SPNDegree, IdealDegree, ThreatLattice)
- **OptiSat**: 190 teoremas de E-graph soundness (SoundRewriteRule, NodeSemantics, ILP extraction)
- **Componentes TrustHash reutilizables**: E-graph core (20 archivos, ~300 teoremas), 12 reglas verificadas, ILP extraction, AutoSboxPipeline, DP over nice trees

### Gaps Identificados

| # | Gap | Criticidad | Estrategia |
|---|-----|-----------|-----------|
| 1 | CryptoDesign como término e-graph (formal) | ALTA | Definir inductive en Lean, bridge a HashExprF |
| 2 | Reglas de reescritura criptográficas (12→30+) | ALTA | Extender con Luby-Rackoff, Wide Trail, S-box substitution |
| 3 | Integración AXLE | MEDIA | API wrapper: verify_proof + repair_proofs en loop |
| 4 | Integración AlphaEvolve/OpenEvolve | MEDIA | MAP-Elites + LLM ensemble como rule proposer |
| 5 | SSD para pre-filtrado | BAJA | Meta-predictor pre-filtra candidatos antes de Lean |
| 6 | RLVF loop operacional | ALTA | Binary reward (Lean compila + TrustHash security improves) |
| 7 | Cost model: latencia y área | MEDIA | Lookup table empírico + Pareto extraction |
| 8 | Extracción multi-objetivo Pareto | ALTA | Adaptar ILP extraction con 3 objetivos |
| 9 | Compositionalidad de seguridad | MEDIA | Probar security(Compose(d1,d2)) = f(security(d1), security(d2)) |
| 10 | Quantum security analysis | BAJA | Grover floor (n/3) ya en TrustHash v4.0 |

---

## 2. Lecciones Aplicables

### Lecciones Reutilizables

| ID | Título | Categoría | Aplicación a SuperHash |
|----|--------|-----------|----------------------|
| **L-530** | Pareto scalarization monotonicity | Multi-Objective | `costPair_scalarize_mono` — puente central para convertir diseños Pareto-óptimos en soluciones numéricas bajo scalarización lineal |
| **L-516** | Mirror inductive para E-Graph extraction | E-Graph Core | Patrón de soundness reutilizable: 1 lema puente por Op, reduce N×M a 1 teorema |
| **L-513** | Compositional End-to-End Pipeline Proofs | Pipeline Verification | Descomponer pipeline: saturate → computeCosts → extract → verify, cada etapa con soundness compositional |
| **L-512** | Three-Tier Bridge Architecture | Production Integration | Shell (LLM proposes) ← no-verificado. Core (saturateF, extractF) ← verificado. Bridge ← composición end-to-end |
| **L-543** | Bridge theorems: generic → hash instances | Generic Frameworks | `generic_framework(specific_params) = specific_definition` — conectar análisis genérico a AES, Keccak, Poseidon |
| **L-550** | Soundness bug: 0^0=1 en Lean | Rewrite Safety | Al escribir reglas pow(0,n)→0, guardar con n+1 pattern. Aplica a reglas criptográficas |
| **L-269** | LLM QA false positives | LLM Integration | Kernel verification > LLM analysis. Protocolo: si Lean verifica y LLM critica, confiar en Lean |
| **L-351** | Example-based verification insuficiente | Structural Proofs | Inducción estructural > ejemplos selectivos. Aplica a CryptoDesign properties |

### Anti-Patrones a Evitar

1. **Identity passes disfrazados** (`:= id` en pipeline) — deuda técnica silenciosa
2. **0^0 unsoundness** — reglas pow(0,_) sin guardia n≥1
3. **LLM over-confidence** — LLM asume semántica incorrecta, critica código verificado
4. **Example-based false proof** — decidir 8 casos ≠ prueba formal para todos
5. **Refactor-to-verify** — no probar código de producción directamente; crear core verificado alternativo

### Top 5 Lecciones Críticas

1. **L-530** (MÁXIMA): Pareto scalarization — puente matemático directo para multi-objetivo
2. **L-516** (MÁXIMA): Mirror inductive — evita explosión combinatoria de soundness theorems
3. **L-513** (MÁXIMA): Pipeline compositional — estructura obligatoria para pipeline multi-etapa
4. **L-512** (ALTA): Three-tier bridge — única arquitectura viable para LLM + verification
5. **L-269** (MEDIA-ALTA): LLM false positives — establece protocolo Lean > LLM

---

## 3. Bibliografía Existente Relevante

### Documentos Clave por Eje

#### Eje 1: Equality Saturation + E-graphs

| Documento | Año | Contribución |
|-----------|-----|-------------|
| **egg: Fast and Extensible Equality Saturation** (Willsey et al.) | 2021 | Arquitectura moderna de e-graphs, rebuilding, e-class analysis |
| **E-Graphs as Circuits, and Optimal Extraction via Treewidth** (Sun et al.) | 2024 | Conexión e-graphs ↔ Boolean circuits, DP via tree decompositions |
| **Fast and Optimal Extraction for Sparse Equality Graphs** (Goharshady et al.) | 2024 | Treewidth-based extraction para e-graphs dispersos |
| **SmoothE: Differentiable E-Graph Extraction** (Cai et al.) | 2025 | Extracción diferenciable con gradient descent, GPU-acelerada |
| **LGuess: Equality Saturation Guided by LLMs** (Peng et al.) | 2025 | LLM-guided equality saturation para program optimization |
| **Guided Equality Saturation** (Köhler et al.) | 2024 | Semi-automatic: human insight + automated eqsat |
| **Ruler: Rewrite Rule Inference Using Equality Saturation** (Nandi et al.) | 2021 | Inferencia automática de rewrite rules via eqsat |

#### Eje 2: Lean 4 + E-graphs

| Documento | Año | Contribución |
|-----------|-----|-------------|
| **Lean-egg: Equality Saturation Tactic for Lean** (Rossel & Goens) | 2026 | POPL 2026: equality saturation como táctica de demostración en Lean |
| **DeepSeek-Prover-V2** (Ren et al.) | 2025 | GRPO training, binary Lean feedback, 88.9% MiniF2F-test |
| **LeanDojo** (Yang et al.) | 2023 | Toolkit: extracción de datos de Lean, premise selection |
| **Verifying Peephole Rewriting in SSA Compiler IRs** (Bhat et al.) | 2024 | Verificación de rewrite rules en Lean 4 |

#### Eje 3: Criptografía de Hash

| Documento | Año | Contribución |
|-----------|-----|-------------|
| **POSEIDON: Hash for ZK Proof Systems** (Grassi et al.) | 2023 | Diseño original: sponge + partial/full rounds |
| **Ethereum Poseidon Bounties** (Bak et al.) | 2025 | Ataques exitosos: polynomial system solving |
| **Skipping Class** (Merz & Rodríguez) | 2026 | Round-skipping via tensor structures |
| **Evolutionary Approach to S-box Generation** (Kuznetsov et al.) | 2024 | GA para S-boxes con nonlinearity 104 |

#### Eje 4: Síntesis Automática

| Documento | Año | Contribución |
|-----------|-----|-------------|
| **ASPEN: LLM-Guided E-Graph Rewriting for RTL** (Deng et al.) | 2025 | 3 agentes: rule proposal, selection, PPA feedback — 16.51% area improvement |
| **ROVER: RTL Optimization via Verified E-Graph Rewriting** (Coward et al.) | 2024 | Verificación formal de rewriting en hardware |
| **E-morphic: Scalable Equality Saturation for Logic Synthesis** (Chen et al.) | 2023 | Equality saturation para síntesis de lógica digital |

### Grafo de Conceptos

```
Equality Saturation (w=0.9)
├── E-graphs (w=0.8)
├── Rewrite Rules (w=0.7)
├── Congruence Closure (w=0.7)
├── E-graph Extraction (w=0.9) ←── Treewidth DP (w=0.8)
├── LLM-guided Optimization (w=0.5) ←── AlphaEvolve
└── Lean-egg tactic (w=0.8) ←── Lean 4 integration

Algebraic Cryptanalysis (w=0.8)
├── Polynomial System Solving (w=0.8)
├── Gröbner Basis Attacks (w=0.8)
├── Round-Skipping (w=0.6) ←── Skipping Class
└── Key-Recovery (w=0.8)
```

### Gaps Bibliográficos

| Gap | Descripción | Relevancia |
|-----|------------|-----------|
| AXLE integration patterns | Cómo integrar AXLE en loops LLM+Lean | ALTA |
| RLVF for rewrite rules | RL con señal binaria de Lean para rules, no proofs | ALTA |
| Quantum security in design space | Análisis post-cuántico automatizado | MEDIA |
| Benchmark suite for hash crypto | Estándar verificado tipo NIST | ALTA |
| RL-based rule scheduling | RL para decidir orden de aplicación de rules | MEDIA |

---

## 4. Estrategias y Decisiones Previas

### Estrategias Ganadoras

| Estrategia | Proyecto Fuente | Resultado |
|-----------|----------------|-----------|
| **Two-layer security model** (min(generic, structural)) | TrustHash | 2,160 teoremas, 6 hash instances verificadas |
| **Parameters as Nat, no Mathlib** | TrustHash/LeanHash | Compilación <60s, 0 axioms, 0 sorry |
| **E-graph + ILP extraction** | TrustHash/OptiSat | Pipeline completo con soundness end-to-end |
| **Mirror inductive for e-graph** | OptiSat | 1 lema puente vs N×M explosión |
| **Topological DAG + close_block** | All projects | Zero regressions across 5+ projects |
| **Copy/adapt from libraries** | All projects | Autonomía de compilación, no coupling |
| **spec_audit.py for quality** | TrustHash v4.0 | T1=0, T2=0 tras auditoría exhaustiva |

### Decisiones Arquitecturales Aplicables

| Decisión | Justificación | Aplica a SuperHash |
|---------|--------------|-------------------|
| Lean 4 sin Mathlib (TrustHash) | Compilación rápida, sin coupling | SuperHash usará Mathlib (4.28) — diferente |
| Struct fields como Nat, no Finset | Evita complejidad Mathlib | Mantener para métricas, usar Mathlib para álgebra |
| E-graph con fuel (OptiSat) | Terminación garantizada | Reutilizar para saturateF |
| ILP extraction certificate | Verificación post-hoc | Extender a multi-objetivo |
| Non-vacuity examples obligatorios | Prevenir tautologías | Mantener en SuperHash |

### Benchmarks de Referencia

| Métrica | Valor | Proyecto |
|---------|-------|----------|
| Teoremas totales | 2,160 | TrustHash v4.0 |
| Sorry | 0 | TrustHash/OptiSat/LeanHash |
| Build time | <60s | TrustHash (190 archivos) |
| E-graph rules | 12 verified | TrustHash |
| Soundness chain depth | 5 levels | OptiSat pipeline |
| Hash instances analyzed | 6 | TrustHash v4.0 |

### Errores Evitados

| Error | Razón del rechazo | Relevancia |
|-------|-------------------|-----------|
| Mathlib como dependencia en TrustHash | Coupling, build time, version breaks | SuperHash SÍ usa Mathlib — mitigar con pinning |
| Identity passes en pipeline | Ocultan deuda técnica como completitud | Vigilar en pipeline SuperHash |
| Probar código de producción | Imposible con IO/timeouts | Three-tier architecture obligatoria |
| LLM output sin verificación | False positives (L-269) | Binary Lean feedback obligatorio |

---

## 5. Nueva Bibliografía Encontrada (Online Research)

### 5.1 AXLE (Axiom Lean Engine)

**Fuente**: https://axle.axiommath.ai/v1/docs/
**Versión**: v1.0.1 (11 marzo 2026)
**Tipo**: SaaS API + CLI + MCP Server

#### 16 Herramientas

| Herramienta | Función | Uso en SuperHash |
|------------|---------|-----------------|
| `verify_proof` | Validar proof contra statement | Verificación rápida de rules LLM-generadas |
| `check` | Evaluar código Lean (compilación) | Pre-filtro antes de Lean completo |
| `repair_proofs` | Auto-reparar proofs rotos | Reparar sorry en reglas propuestas |
| `sorry2lemma` | Extraer sorry como lemmas standalone | Descomponer proofs complejos |
| `extract_theorems` | Separar archivo en teoremas individuales | Análisis modular |
| `simplify_theorems` | Eliminar tácticas redundantes | Limpieza post-generación |
| `disprove` | Encontrar contraejemplos | Validar no-vacuidad |
| `merge` | Combinar archivos Lean | Integración de módulos |
| `have2lemma` | Extraer have a top-level | Refactoring automático |
| `normalize` | Estandarizar formato | Consistencia |
| `rename` | Renombrar + actualizar refs | Refactoring |
| `theorem2sorry` | Reemplazar proofs con sorry | Templates |
| `have2sorry` | Reemplazar have proofs | Ejercicios |
| `theorem2lemma` | Convertir theorem↔lemma | Refactoring |

#### Rate Limits

| Tier | Requests concurrentes | Timeout |
|------|----------------------|---------|
| Anonymous | 10 | 15 min |
| API key | 20 | 15 min |

#### Limitaciones
- `verify_proof` confía en el entorno Lean — adversarios pueden explotar metaprogramming
- Recomiendan lean4checker, Comparator, o SafeVerify para código no confiable
- Sin benchmarks de velocidad publicados

#### Integración SuperHash
```
LLM propone regla → AXLE.check (fast reject) → AXLE.verify_proof (validate)
  → si falla: AXLE.repair_proofs → si falla: AXLE.sorry2lemma → DeepSeek-Prover
```

### 5.2 AlphaEvolve / OpenEvolve / CodeEvolve

#### AlphaEvolve (DeepMind)
- Concepto: evolución de código algorítmico con LLMs + multi-objective fitness
- No open-source oficial, pero múltiples reimplementaciones

#### OpenEvolve (open-source)
**Fuente**: pypi.org/project/openevolve
- MAP-Elites + LLM ensemble (weighted models)
- Multi-stage cascade evaluation con artifacts
- Island-based populations para diversidad
- Warm-start desde checkpoints
- Feature dimensions configurables: `["complexity", "diversity"]`
- Fitness: `EvaluationResult` con `metrics` (numeric) + `artifacts` (non-numeric)

#### CodeEvolve (open-source)
**Fuente**: github.com/inter-co/science-codeevolve
- Islands-based GA + LLM orchestration
- **Depth exploitation operator**: refinamiento targeted de soluciones prometedoras
- **Inspiration-based crossover**: combinar features semánticas de soluciones exitosas
- **Meta-prompting exploration**: diversidad dinámica del prompt population
- Outperforms AlphaEvolve en varios benchmarks

#### Integración SuperHash
```python
# Fitness function para hash design evolution
def evaluate_design(code: str) -> EvaluationResult:
    metrics = {
        "security": trusthash_security_bits(code),    # via TrustHash pipeline
        "latency": estimate_gate_count(code),          # via circuit model
        "proof_completeness": lean_sorry_count(code),  # via AXLE.check
    }
    return EvaluationResult(metrics=metrics)
```

**MAP-Elites dimensions**: `["construction_type", "security_level"]`
**Warm-start**: AES-128, Poseidon-128, Rescue-Prime-128 como semillas iniciales

### 5.3 Speculative Speculative Decoding (SSD / Saguaro)

**Fuente**: github.com/tanishqkumar/ssd
**Paper**: "Speculative Speculative Decoding" (Tanishq Kumar et al.)

#### Concepto Central
Autoregressive decoding es secuencial. Speculative decoding usa draft model rápido para predecir tokens, verificados en paralelo por target model. **SSD va un paso más**: mientras la verificación está en curso, el draft model **predice los resultados de verificación** y prepara especulaciones pre-emptivamente.

#### Performance
- **2x más rápido** que speculative decoding optimizado
- **5x más rápido** que autoregressive estándar
- Garantía **lossless** (distribución idéntica al target model)

#### Algoritmo Saguaro
1. Draft model genera candidatos
2. Verificación comienza (target model forward pass)
3. **En paralelo**: draft model predice resultados de verificación probable
4. Si predicción acertada → especulación lista inmediatamente → elimina latencia de drafting

#### Integración SuperHash
```
LLM propone regla (draft) → AXLE.verify_proof (verification)
  EN PARALELO: LLM predice si verificación pasará y prepara siguiente regla
  Si predicción = "PASS" → siguiente regla ya lista
  Si predicción = "FAIL" → LLM ya preparó variante reparada
```

**Tres desafíos** identificados por SSD:
1. ¿Cómo predecir verificación antes de que termine? → Heurísticas basadas en historial de rules similares
2. ¿Cómo preparar múltiples outcomes? → Branching: prepare for PASS and FAIL simultaneously
3. ¿Cuándo es rentable especular? → Cost model: verification_time vs speculation_overhead

### 5.4 ASPEN: LLM-Guided E-Graph Rewriting

**Fuente**: Cornell/NVIDIA (MLCAD 2025)

#### Arquitectura de 3 Agentes
1. **Rule Proposal Agent**: Genera reglas design-specific basadas en input + reglas iniciales, verifica corrección
2. **Rule Selection Agent**: Elige subset crítico basado en diseño + historial de exploración
3. **PPA Feedback Agent**: Analiza resultados de síntesis, ajusta e-node weights para guiar extracción

#### Resultados
- **16.51% mejora en área** vs e-graph baselines
- **6.65% mejora en delay**
- Feedback loop iterativo: design → synthesize → analyze → adjust weights → re-extract

#### Transferencia a SuperHash
ASPEN es el **precedente más directo**: LLM propone rules, e-graph aplica, feedback guía extracción. Diferencia: ASPEN opera sobre RTL (hardware), SuperHash sobre CryptoDesign (hash functions). El patrón de 3 agentes es directamente transferible.

### 5.5 DeepSeek-Prover-V2

**Fuente**: arxiv.org/abs/2504.21801

#### Entrenamiento
1. **Cold start**: DeepSeek-V3 descompone problemas en subgoals, sintetiza chain-of-thought
2. **GRPO**: Group Relative Policy Optimization con binary correct/incorrect feedback de Lean
3. **Resultado**: 88.9% pass en MiniF2F-test, 49/658 PutnamBench

#### Integración SuperHash
- Modelo para RLVF loop: binary reward (Lean compila + security improves)
- Subgoal decomposition: descomponer "probar soundness de regla compuesta" en sub-lemmas
- GRPO adaptable: reward = `compile_success * security_improvement`

---

## 6. Insights de Nueva Bibliografía

### Insight 1: ASPEN valida la arquitectura SuperHash

ASPEN (Cornell/NVIDIA 2025) demuestra que LLM-guided e-graph rewriting funciona en producción para optimización de hardware. El patrón de 3 agentes (rule proposal → rule selection → feedback) es directamente transferible a SuperHash. La diferencia clave es que SuperHash necesita **soundness formal** (Lean proofs) mientras ASPEN usa verificación empírica (simulation).

### Insight 2: AXLE resuelve el cuello de botella de verificación

El launch de AXLE v1.0 (marzo 2026) con 16 herramientas y rate limits generosos (10-20 concurrent, 15min timeout) hace viable un loop rápido LLM→verify. El pipeline: `check` (fast reject) → `verify_proof` → `repair_proofs` → `sorry2lemma` permite cascada de fallbacks sin bloquear el loop.

### Insight 3: OpenEvolve/CodeEvolve proveen el framework de evolución

No hay que implementar MAP-Elites desde cero. OpenEvolve (pypi) y CodeEvolve (GitHub) proveen: LLM ensemble, island populations, warm-start, multi-stage evaluation, checkpoints. Solo hay que definir el fitness function (`security × latency × proof_completeness`).

### Insight 4: SSD es aplicable pero con adaptación significativa

SSD (Saguaro) está diseñado para LLM token generation, no para formal verification. La transferencia a SuperHash requiere redefinir "draft" = LLM propone regla, "verification" = AXLE/Lean verifica, "meta-predictor" = historial de éxito por tipo de regla. El beneficio potencial (2x speedup en el loop) justifica la adaptación.

### Insight 5: DeepSeek-Prover-V2 valida RLVF

El training de DeepSeek-Prover-V2 con binary Lean feedback + GRPO alcanza 88.9% en MiniF2F. Esto valida que **binary reward de proof assistant es suficiente** para entrenar modelos útiles. SuperHash puede usar el mismo approach pero con reward compuesto: `lean_compiles AND security_improved`.

### Insight 6: Lean-egg (POPL 2026) integra eqsat en Lean 4

Rossel & Goens (POPL 2026) implementaron equality saturation como táctica de Lean. Esto permite que **las reglas de reescritura se verifiquen dentro de Lean** usando la táctica `eqsat`. Implicación: SuperHash puede tener un pipeline 100% dentro de Lean: proponer regla → verificar con eqsat → aplicar.

---

## 7. Síntesis de Insights

### Hallazgos Clave (Top 10)

1. **ASPEN valida la arquitectura**: LLM-guided e-graph rewriting funciona en producción (16% area improvement en RTL). El patrón de 3 agentes es directamente transferible.

2. **AXLE resuelve verificación rápida**: 16 herramientas, rate limits generosos, pipeline de fallback (check → verify → repair → sorry2lemma). Disponible desde marzo 2026.

3. **OpenEvolve/CodeEvolve listos**: MAP-Elites + LLM ensemble open-source. Solo definir fitness function: `security(TrustHash) × 1/latency × proof_completeness(AXLE)`.

4. **DeepSeek-Prover-V2 valida RLVF**: Binary Lean feedback + GRPO = 88.9% en MiniF2F. Reward: `lean_compiles ∧ security_improved`.

5. **Lean-egg (POPL 2026)**: Equality saturation como táctica de Lean. Pipeline 100% dentro de Lean es posible.

6. **SSD adaptable**: Meta-predicción de verificación reduce latencia del loop 2x. Requiere redefinir draft/verification/predictor.

7. **LGuess**: LLM-guided equality saturation ya demostrado para program optimization. Transferible a crypto design.

8. **E-Graphs as Circuits (Sun 2024)**: Optimal extraction via treewidth — conecta directamente con TrustHash's DP optimality.

9. **Three-tier architecture (L-512)**: Única arquitectura viable para LLM + verification — Shell (LLM) / Core (Lean) / Bridge (composición).

10. **Pareto scalarization (L-530)**: Puente matemático para multi-objetivo — scalarización preserva optimalidad Pareto.

### Riesgos Identificados

| Riesgo | Nivel | Mitigación |
|--------|-------|-----------|
| LLM genera reglas unsound | ALTO | AXLE.verify_proof + lean4checker para código no confiado |
| Mathlib coupling (SuperHash en 4.28) | MEDIO | Pin versión, builds incrementales |
| AXLE rate limits insuficientes | BAJO | API key tier (20 concurrent), caché local |
| E-graph explosion (muchas reglas) | MEDIO | Rule selection agent (ASPEN pattern) + fuel limit |
| RLVF reward hacking | MEDIO | Reward shaping + non-vacuity checks |
| Lean-egg compatibility con 4.28 | MEDIO | Verificar versión de Lean-egg disponible |

### Recomendaciones para Planificación

1. **Fase 0 (De-risk)**: Implementar CryptoDesign type + 3 reglas verificadas + extractAcion from e-graph con 1 objetivo
2. **Fase 1 (Core E-graph)**: Adaptar OptiSat SoundRewriteRule para CryptoDesign, extender a 15+ reglas
3. **Fase 2 (Multi-objetivo)**: Implementar Pareto extraction con 3 objetivos (security, latency, gates)
4. **Fase 3 (LLM loop)**: Integrar OpenEvolve/CodeEvolve con fitness = TrustHash evaluation
5. **Fase 4 (AXLE)**: Integrar AXLE para verificación rápida en el loop
6. **Fase 5 (RLVF)**: Training loop inspirado en DeepSeek-Prover-V2 con GRPO

### Recursos Prioritarios

1. **ASPEN paper** (Cornell/NVIDIA 2025) — patrón de 3 agentes directamente transferible
2. **Lean-egg (POPL 2026)** — equality saturation como táctica de Lean
3. **OpenEvolve** (pypi) — framework de evolución ready-to-use
4. **DeepSeek-Prover-V2** (arxiv 2504.21801) — GRPO + binary Lean feedback
5. **E-Graphs as Circuits** (Sun 2024) — optimal extraction via treewidth

---

## 8. Teoremas Extraídos

### Por Grupo Temático

| Grupo | Cantidad | Dificultad Promedio |
|-------|----------|-------------------|
| Design Space Foundations | 4 defs + 2 theorems | easy |
| Pareto Dominance | 1 struct + 3 theorems | easy-medium |
| Rewrite Rule Soundness | 1 struct + 2 theorems | medium |
| Concrete Instances | 3 examples | easy |

### Orden de Dependencias

```
CryptoConstruction (inductive)
  └── DesignParams (structure)
       ├── designAlgDegree (def) → degree_mono_rounds (theorem)
       ├── designActiveSboxes (def) → active_sboxes_mono_rounds (theorem)
       └── SecurityMetrics (structure)
            ├── dominates (def) → dominates_irrefl, dominates_trans
            └── SoundRewriteRule (structure) → compose_sound
```

---

## 9. Formalización Lean 4

### Resumen

| Métrica | Valor |
|---------|-------|
| Archivo | `LeanHash/DesignSpace.lean` |
| Toolchain | Lean 4.16.0 (sin Mathlib) |
| Definiciones | 8 (1 inductive, 3 structures, 4 defs) |
| Teoremas | 12 (todos probados, 0 sorry) |
| Non-vacuity examples | 3 |
| Instancias concretas | 2 (AES-128, Poseidon-128) |
| Axiomas usados | propext, Quot.sound (estándar Lean) |
| Build | **PASS** (lake build, 0 errors, 0 warnings) |

### Tipos y Definiciones

| Nombre | Tipo | Descripción |
|--------|------|-------------|
| `CryptoConstruction` | inductive | SPN, Feistel, Sponge, ARX |
| `DesignParams` | structure | stateWidth, sboxDegree, numRounds, branchNumber (con invariantes h_*_pos) |
| `SecurityMetrics` | structure | securityBits, latency, gateCount (para optimización multi-objetivo) |
| `SoundRewriteRule` | structure | name, transform, preserves_security (regla verificada) |
| `designAlgDegree` | def | sboxDegree^numRounds |
| `designActiveSboxes` | def | branchNumber * numRounds |
| `dominates` | def | Pareto dominance relation (≥ en todo, > en al menos uno) |
| `composeRules` | def | Composición de reglas sound → regla sound |

### Teoremas Formalizados (12 teoremas, 0 sorry)

| # | Nombre | Statement | Axiomas |
|---|--------|-----------|---------|
| 1 | `degree_mono_rounds` | d.sboxDegree ≥ 2 → designAlgDegree d ≤ designAlgDegree {d with numRounds += extra} | propext, Quot.sound |
| 2 | `active_sboxes_mono_rounds` | designActiveSboxes d ≤ designActiveSboxes {d with numRounds += extra} | propext, Quot.sound |
| 3 | `active_sboxes_mono_branch` | designActiveSboxes d ≤ designActiveSboxes {d with branchNumber += extra} | propext, Quot.sound |
| 4 | `dominates_irrefl` | ¬ dominates a a | propext, Quot.sound |
| 5 | `dominates_trans` | dominates a b → dominates b c → dominates a c | propext, Quot.sound |
| 6 | `dominates_asymm` | dominates a b → ¬ dominates b a | propext, Quot.sound |
| 7 | `compose_sound` | ∀ d, designAlgDegree ((composeRules r1 r2).transform d) ≥ designAlgDegree d | (ninguno) |
| 8 | `aes128_alg_degree` | designAlgDegree aes128Design = 7^10 | rfl |
| 9 | `aes128_active_sboxes` | designActiveSboxes aes128Design = 50 | native_decide |
| 10 | `aes128_degree_exceeds` | designAlgDegree aes128Design ≥ 2^28 | native_decide |
| 11 | `poseidon128_alg_degree` | designAlgDegree poseidon128Design = 5^8 | rfl |
| 12 | `poseidon128_active_sboxes` | designActiveSboxes poseidon128Design = 32 | native_decide |

---

## 10. Librería Generada

- **Nombre**: LeanHash
- **Path**: `/Users/manuelpuebla/Documents/claudio/leanhash/`
- **Mathlib**: No (v4.16.0)
- **Módulos totales**: 13 (12 existentes + 1 nuevo: DesignSpace)
- **Nuevo módulo**: `LeanHash/DesignSpace.lean` (~280 líneas)
- **Teoremas totales librería**: ~146 (134 existentes + 12 nuevos)
- **Build**: **OK** (`lake build` — 16/16 módulos, 0 errors, 0 warnings)
- **Uso**: Copiar/adaptar teoremas al proyecto SuperHash (NUNCA importar como dependencia lake)

---

## 11. Código Reutilizable de Proyectos Internos

Análisis profundo de 4 librerías internas (OptiSat, VR1CS-lean, SuperTensor-lean, AMO-lean) para identificar estructuras, tipos y patrones directamente adaptables a SuperHash.

### 11.1 OptiSat (~190 teoremas, ~9,280 LOC)

**Path**: `~/Documents/claudio/optisat/`

**Estructuras clave reutilizables**:

| Estructura | Archivo | SuperHash Use |
|------------|---------|---------------|
| `EGraphState` | EGraph/Core.lean | E-graph engine parametrizado por Op — instanciar con CryptoOp |
| `ConsistentValuation` | EGraph/ConsistentValuation.lean | Invariante maestro: semántica preservada a través de merge/saturación |
| `NodeSemantics` typeclass | EGraph/NodeSemantics.lean | Interface genérica para operaciones en el e-graph |
| `SoundRewriteRule` | EGraph/SoundRewriteRule.lean | Reglas con prueba de soundness embebida — core de exploration |
| `Extractable` typeclass | EGraph/Extractable.lean | Interface verificada para extraction (greedy/ILP/DP) |
| `ILPCertificate` | ILP/ILPCertificate.lean | Verificación de certificados ILP (solver externo no-trusted) |
| `full_pipeline_soundness` | Pipeline/Soundness.lean | Teorema composicional: saturación → cost → extraction → correctness |

**Cadena de soundness** (directamente adaptable):
```
saturate_sound ∘ merge_preserves_consistency ∘ extract_correct = full_pipeline_soundness
```

**Patrón de extraction triple**:
1. **Greedy** (fuel-based): `extractF_correct` — rápido, subóptimo
2. **ILP** (certificate): `extractILP_correct` — óptimo global, solver externo verificado
3. **Treewidth DP**: `dp_optimal_of_validNTD` — óptimo para grafos de treewidth acotado

**Adaptación para SuperHash**: Instanciar `NodeSemantics` con operaciones criptográficas (S-box, capa lineal, XOR, round). Cada `SoundRewriteRule` preserva la seguridad algebraica del diseño hash.

### 11.2 VR1CS-lean (~2,219 teoremas, ~29.7K LOC)

**Path**: `~/Documents/claudio/vr1cs-lean/`

**Estructuras clave reutilizables**:

| Estructura | Archivo | SuperHash Use |
|------------|---------|---------------|
| `CircuitExpr` | VR1CS/Basic.lean | DSL para expresiones aritméticas sobre ZMod p — base para hash computations |
| `R1CSPreservation` | Soundness/PipelineE2E.lean | Framework composicional: cada pass prueba `satisfies_r1cs r w → satisfies_r1cs (pass r) w` |
| `VerifiedOptConfig` | Soundness/VerifiedPipeline.lean | Config de optimización con prueba embebida de soundness |
| `R1CSCostModel` | CostModel.lean | Costos parametrizables por backend (Groth16/PLONK/STARK) |
| `WitnessMap` | WitnessMap.lean | Tracking de transformaciones de witness en optimizaciones |
| `GateRegistry` | Extended.lean | Registry de gates custom — ya incluye `gateIdPow5` (Poseidon S-box) |
| `CCSInstance` | CCS.lean | Unificación multi-backend (R1CS, Plonkish, AIR) |
| `FieldConfig` | Field/Setup.lean | Configuración de campo primo con prueba de primalidad |
| 101 rewrite rules | Rules/*.lean | 22 ring + 17 field + 10 Plonky2 + 11 crypto gadgets (Poseidon sbox5, MiMC) |

**Patrón de pipeline verificado**:
```
gaussianElim → eqsat_optimization → cse_detection → sub_elimination → lookup_detection
```
Cada paso es un `R1CSPreservation` composable. End-to-end: `pipeline_e2e_sound`.

**Reglas crypto ya formalizadas**: `pow5_identity`, `pow5_composition` (Poseidon S-box), MiMC cube rules, EdDSA gadgets. Proof pattern: `simp [CircuitExpr.eval]; ring` sobre `ZMod p`.

**Bridge R1CS ↔ CircuitExpr**: `r1cs_constraint_soundness` prueba equivalencia semántica entre representaciones — justifica que optimizaciones sobre CircuitExpr preservan satisfacibilidad R1CS.

### 11.3 SuperTensor-lean (~2,219 teoremas, v3.6.1)

**Path**: `~/Documents/claudio/supertensor-lean/`

**Estructuras clave reutilizables**:

| Estructura | Archivo | SuperHash Use |
|------------|---------|---------------|
| `TensorExpr` (type-indexed) | Tensor/Basic.lean:109 | Template para `CryptoDesign` AST con constraints en el tipo |
| `TensorSigma` (loop IR) | Sigma/Basic.lean:153 | Template para `AnalysisSchedule` (differential trails, SAT queries) |
| `ENodeOps` typeclass | EGraph/Ops.lean:21 | Interface genérica verificada con 4 axiomas — copiar tal cual |
| `EGraph (Op : Type)` | EGraph/Core.lean:115 | E-graph parametric engine — copiar sin cambios |
| `SoundTensorRule` | Rules/SoundRule.lean:43 | Template para `SoundCryptoRule` con proof de security preservation |
| `ConditionalTensorRule` | Rules/SoundRule.lean | Reglas con side-conditions (e.g., "solo si S-box input es válido") |
| `SemanticPreservation` | Sigma/SemanticPreservation.lean:46 | Composición CompCert-style de pruebas de correctness multi-pass |
| `ILPSolution` + checkers | Extraction/ILPCertificate.lean:36 | Trust boundary reduction: verificar output de solver externo |
| `TensorCostModel` | Cost/Basic.lean:54 | Template para `CryptoCostModel` pluggable |
| Translation Validation | EGraph/TranslationValidation.lean | 14 congruence theorems para verificar equivalencia post-extraction |

**Two-Level Compilation** (patrón principal):
```
TensorExpr → addToEGraph → saturate → extract → TensorExtractedExpr → lower → TensorSigma → codegen
```
Cada paso tiene `SemanticPreservation`. SuperHash: `CryptoDesign → saturate → extract → AnalysisSchedule → codegen`.

**Lecciones clave**:
- `List Nat` para shapes evita "dependent type hell" (L-082) — usar principio similar para design params
- Cost model NO está en el TCB — solo afecta performance, no correctness (I-053)
- `custom` constructor en el AST permite blackboxing de operaciones opacas

### 11.4 AMO-lean (~1,041 teoremas, 173 archivos)

**Path**: `~/Documents/claudio/amo-lean/`

**Estructuras clave reutilizables**:

| Estructura | Archivo | SuperHash Use |
|------------|---------|---------------|
| E-graph engine | AMO/EGraph/*.lean | Comparte herencia con OptiSat — mismo patrón NodeSemantics |
| `FieldConfig` (FRI) | AMO/FRI/FieldConfig.lean | Configs para Goldilocks, BabyBear — campos ZK-friendly |
| `Vec α n` / `Matrix` | AMO/Vectors/*.lean | Tipos de vector/matrix con proofs de bounds |
| `LowLevelExpr` | AMO/CodeGen/*.lean | Representación SSA para code generation |
| FRI protocol | AMO/FRI/*.lean | Soundness de verificación FRI — útil para STARK backend |
| Code generation | AMO/CodeGen/Pipeline.lean | Pipeline completo: expression → SSA → C/Rust |

**Patrón de code generation**:
```
HighLevelExpr → lower → LowLevelExpr (SSA) → emit → String (C/Rust)
```
SuperHash puede adaptar para generar implementaciones de hash optimizadas automáticamente.

### 11.5 Matriz de Reutilización Cruzada

| Componente SuperHash | OptiSat | VR1CS | SuperTensor | AMO |
|----------------------|---------|-------|-------------|-----|
| **CryptoDesign AST** | — | CircuitExpr | TensorExpr (best template) | — |
| **E-graph engine** | EGraphState | EGraph/Core | EGraph (Op) (best: parametric) | EGraph (herencia OptiSat) |
| **Rewrite rules** | SoundRewriteRule | 101 rules (crypto incluidas) | SoundTensorRule | — |
| **Extraction** | Triple (greedy/ILP/DP) | ILP encode | ILP certificate check | — |
| **Pipeline soundness** | full_pipeline_soundness | pipeline_e2e_sound | SemanticPreservation | — |
| **Cost models** | — | R1CSCostModel (multi-backend) | TensorCostModel (pluggable) | — |
| **Field configs** | — | FieldConfig + Goldilocks | — | FieldConfig (FRI) |
| **Code generation** | — | — | lower + codegen | LowLevelExpr (SSA) |
| **NodeSemantics** | Typeclass (origin) | CircuitNodeOp | ENodeOps (evolved) | Herencia OptiSat |
| **ZK integration** | — | CCS (multi-backend) | — | FRI soundness |

### 11.6 Recomendaciones de Adaptación

**Prioridad 1 — Copiar directamente** (sin cambios o cambios mínimos):
1. `ENodeOps` typeclass de SuperTensor (4 axiomas verificados)
2. `EGraph (Op : Type)` engine de SuperTensor (parametric, 0 sorry)
3. `SemanticPreservation` + `compose_preservation` de SuperTensor
4. `ILPSolution` + 4 decidable checkers de SuperTensor

**Prioridad 2 — Adaptar con cambios moderados**:
1. `SoundRewriteRule` → `SoundCryptoRule` (cambiar dominio de tensor a crypto)
2. `TensorExpr` → `CryptoDesign` (reemplazar constructores tensor por crypto primitives)
3. `R1CSCostModel` → `CryptoCostModel` (añadir S-box cost, treewidth, differential cost)
4. 101 rewrite rules de VR1CS → extraer las 11 crypto gadget rules + añadir nuevas

**Prioridad 3 — Inspiración arquitectural** (no copiar, sino seguir el patrón):
1. Two-level compilation de SuperTensor (CryptoDesign → AnalysisSchedule)
2. Trust boundary de VR1CS (solver externo → certificate → verified check)
3. Pipeline composicional de OptiSat (full_pipeline_soundness como master theorem)
4. Code generation de AMO (LowLevelExpr SSA → C/Rust)

### 11.7 Estadísticas Agregadas

| Proyecto | Teoremas | LOC | Archivos | Mathlib |
|----------|----------|-----|----------|---------|
| OptiSat | ~190 | ~9,280 | ~50 | No |
| VR1CS-lean | ~2,219 | ~29,700 | ~80 | No (ZMod local) |
| SuperTensor | ~2,219 | ~29,700 | ~70 | No |
| AMO-lean | ~1,041 | ~15,000 | 173 | No |
| **Total consultable** | **~5,669** | **~83,680** | **~373** | — |

Todos los proyectos compilan sin Mathlib (Lean 4 v4.16.0 Init/Std only), lo cual es compatible con el toolchain actual de TrustHash. Para SuperHash (target: Lean 4.28 con Mathlib), los teoremas se adaptarían fácilmente al superset.
