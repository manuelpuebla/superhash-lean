# Insights: SuperHash v2.0 — LLM-Guided Rule Discovery + RLVF + Autonomous Design Loop

**Fecha**: 2026-03-13
**Dominio**: lean4
**Estado del objeto**: upgrade (v1.0 complete: 27 files, ~9017 LOC, 0 sorry, 0 axioms)
**Profundidad**: deep (8 agentes)

---

## 1. Analisis del Objeto de Estudio

### Resumen

SuperHash v2.0 extends the verified hash design pipeline (v1.0) with three new capabilities: (1) **LLM-guided rule discovery** via evolutionary search (AlphaEvolve/CodeEvolve pattern), (2) **RLVF training loop** with binary Lean kernel feedback, and (3) **autonomous design loop** that iteratively discovers rules, saturates, extracts Pareto-optimal designs, and expands the rule set. Additionally, v2.0 addresses gaps identified in v1.0: recursive CryptoDesign types, concrete crypto semantics (BitVec/GF(2^k)), and expanded threat models.

### V1.0 Achievement (Foundation)

- 27 .lean files, ~9017 LOC, 29 build jobs
- 323+ theorems, zero sorry, zero axioms
- Pipeline: saturateF -> computeCostsF -> extractPareto (3-part master theorem)
- 8 verified rules (5 EquivalenceRule + 5 PatternSoundRule)
- CryptoOp: 8 flat constructors (sbox, linear, xor, round, compose, parallel, iterate, const)
- Pareto extraction via scalarization (convex hull only)
- Lean 4.28.0, no Mathlib

### V2.0 Scope (This Plan)

| Component | Status | Target |
|-----------|--------|--------|
| CryptoOp extension (hierarchical blocks) | Not started | spnBlock, feistelBlock, spongeBlock, arxBlock |
| Rule discovery (LLM + evolutionary) | Not started | 30+ verified rules from LLM proposals |
| RLVF training loop | Not started | Binary Lean feedback + multi-level rewards |
| Autonomous design loop | Not started | discover -> saturate -> extract -> evaluate -> expand |
| Concrete semantics | Not started | BitVec for S-box, bv_decide proofs |
| Three-layer proving pipeline | Not started | AXLE -> DeepSeek-Prover -> fine-tuned model |
| Expanded threat model | Not started | Slide attacks, invariant subspace, quantum |

### Keywords (22)

equality saturation, e-graphs, egglog, LLM-guided rewriting, RLVF, GRPO, AlphaEvolve, CodeEvolve, MAP-Elites, ASPEN, LGuess, Enumo/Chompy, SmoothE, BitVec, bv_decide, GaloisField, CryptoDesign, Pareto extraction, AXLE MCP, DeepSeek-Prover-V2, Seed-Prover, three-tier bridge

---

## 2. Lecciones Aplicables

### Lecciones Reutilizables

| ID | Titulo | Categoria | Aplicacion a SuperHash v2.0 |
|----|--------|-----------|---------------------------|
| **L-513** | Compositional End-to-End Pipeline Proofs | Pipeline Soundness | CRITICO: v2.0 expandira etapas (discovery -> verify -> saturate -> extract). Cada etapa = soundness composicional |
| **L-572** | Three-Tier Bridge pattern | Architecture | CRITICO: LLM en Tier 1 (IO/TCB), verified core en Tier 2, composition en Tier 3. Translation Validation cierra gap |
| **L-516** | Mirror inductive para E-Graph extraction | E-Graph Core | CRITICO: LLM generara rules mas complejas. Mirror inductive escala linealmente vs explosion combinatoria |
| **L-311** | Transparent Soundness Contract: Three-Part Invariant | Pipeline Soundness | CRITICO: Contrato transparent para pipeline opaco con LLM |
| **L-530** | Pareto scalarization monotonicity | Multi-Objective | Puente matematico para multi-objetivo en v2.0 |
| **L-394** | PatternSoundRule decomposition | Modularidad | Cada regla LLM-propuesta = instance PatternSoundRule independiente |
| **L-310** | Pipeline Wiring via Generic Typeclasses | Architecture | Multiples backends de descubrimiento (LLM, SAT, heuristics) via typeclasses |
| **L-269** | LLM QA false positives | LLM Integration | REGLA DURA: kernel verification > LLM analysis |
| **L-486** | Kernel reduction depth for complex patterns | Pattern Matching | v2.0 rules con 4+ params necesitan unfold + rfl |
| **L-199** | native_decide falla con proof fields | Structs | Preferir pruebas algebraicas sobre native_decide en structs con proofs |

### Anti-Patrones

1. **Identity passes** (`:= id` en pipeline) -- deuda tecnica silenciosa
2. **0^0 unsoundness** -- reglas pow(0,_) sin guardia n>=1
3. **LLM over-confidence** (L-269) -- LLM asume semantica incorrecta, critica codigo verificado
4. **native_decide con proof fields** (L-199) -- falla con "free variables"
5. **Monolithic PreservesCV** -- descomponer en obligaciones independientes (L-394)

### Top 5 Criticas

1. **L-513**: Pipeline compositivo = cimiento de expansion modular
2. **L-572**: Three-Tier Bridge = unica arquitectura viable para LLM + verification
3. **L-516**: Mirror inductive = evita explosion al agregar nuevas familias de reglas
4. **L-311**: Contrato transparent = especificacion formal del pipeline ante auditoria
5. **L-269**: LLM output -> PatternSoundRule instance -> Lean kernel verifica

---

## 3. Bibliografia Existente Relevante

### Documentos Clave por Eje

#### Eje 1: E-graphs + Equality Saturation
- **egg** (Willsey 2021) -- Arquitectura moderna de e-graphs
- **E-Graphs as Circuits** (Sun 2024) -- Treewidth extraction
- **SmoothE** (Cai 2025, ASPLOS Best Paper) -- Extractacion diferenciable, 8x-37x speedup
- **LGuess** (Peng 2025) -- LLM-guided equality saturation
- **Ruler** (Nandi 2021) -- Inferencia automatica de rewrite rules
- **Enumo** (OOPSLA 2023) -- Supersedes Ruler; DSL for theory exploration
- **Chompy** -- Conditional rewrite rule inference

#### Eje 2: LLM-Guided Synthesis
- **ASPEN** (Cornell/NVIDIA 2025) -- 3 agentes: rule proposal, selection, PPA feedback; 16.51% area improvement
- **AlphaEvolve** (DeepMind 2025) -- MAP-Elites + LLM ensemble (Gemini Flash + Pro)
- **CodeEvolve** (inter-co 2025) -- Island GA + LLM; open-source; matches AlphaEvolve
- **RULEFLOW** (Singh 2026) -- Hybrid LLM+Compiler rewrite generation
- **AlphaVerus** (CMU 2024) -- Treefinement: tree search using verifier errors

#### Eje 3: Formal Theorem Proving
- **DeepSeek-Prover-V2** (2025) -- 88.9% miniF2F, subgoal decomposition via sorry, open-source 671B
- **Seed-Prover 1.5** (ByteDance 2025) -- 88% PutnamBench, 5/6 IMO 2025, agentic
- **LeanDojo v2** (Yang 2023) -- Premise retrieval, ReProver, tracing pipeline
- **AXLE** (Axiom 2026) -- MCP server, 14 tools, repair_proofs, lean-4.28.0
- **Goedel-Prover-V2** (2025) -- Self-correction, scaffolded synthesis

#### Eje 4: Criptografia Hash
- **Poseidon/Poseidon2** (Grassi) -- SPN for ZK; MDS matrices; algebraic cryptanalysis
- **Skyscraper** (Bouvier 2024) -- Feistel + MDS for large fields
- **HADES Algebraic Cryptanalysis** (Ashur 2023) -- Grobner basis complexity
- **Rescue-Prime** (Szepieniec 2020) -- Arithmetization-oriented

### Gaps Bibliograficos Criticos

| Gap | Descripcion | Relevancia |
|-----|------------|-----------|
| RLVF for crypto rewrite rules | RL con senal binaria de Lean para rules | ALTA |
| Evolutionary search for hash design | NAS + genetic algorithms para hash | ALTA |
| Speculative proof generation | Draft model para proofs en paralelo | MEDIA |
| AutoFormalization crypto specs | Hash papers -> Lean 4 specs | MEDIA |
| Multi-objective Pareto in e-graphs | Formal Pareto extraction | ALTA |

---

## 4. Estrategias y Decisiones Previas

### Estrategias Ganadoras

| Estrategia | Proyecto | Resultado | Aplicacion v2.0 |
|-----------|---------|-----------|-----------------|
| Typeclass-parametrized e-graph | OptiSat | 363 thms, 0 sorry | Extend NodeOps con RuleCandidateOps |
| Pattern.eval denotational semantics | OptiSat v1.0 | Eliminated PreservesCV | LLM-discovered rules certified via Pattern.eval |
| Three-Tier Bridge (Shell/Core/Spec) | OptiSat v1.3-1.5 | Unified extraction | LLM en Shell, verified core, spec composition |
| Fuel-bounded saturation | OptiSat/SuperHash | Terminacion garantizada | RLVF ajusta fuel por ronda |
| Copy-not-import libraries | All projects | Zero coupling | Copiar verificacion infrastructure, no depender |
| Two-level rules (equiv/improvement) | SuperHash v1.0 | 8 concrete rules | Clasificar rules LLM en equiv/improvement/heuristic |
| Non-vacuity mandatory | SuperHash v1.0 | T4 compliance | Cada regla LLM necesita concrete example |
| DP-optimal extraction via treewidth | OptiSat v1.4 | dp_optimal_of_validNTD | Multi-objective Pareto via DP |

### Decisiones Arquitecturales

| Decision | Justificacion | v2.0 |
|---------|--------------|------|
| Val := Nat | Metricas abstractas; BitVec para v2.0 | Mantener abstract layer; agregar concrete layer |
| Sin Mathlib | Build <60s, zero coupling | BitVec built-in; Mathlib solo si GaloisField necesario |
| Fuel termination | No need for well-founded ordering | RLVF ajusta fuel per round |
| Pareto via scalarizacion | Convex hull OK para v1.0 | SmoothE para non-linear costs en v2.0 |

### Errores Evitados

- Manual rule enumeration no escala (8 -> 50+ rules) -> parametric verification
- Linear scalarization solo convex hull -> SmoothE/epsilon-constraint
- Static rule list -> dynamic rule pool con saturateF_with_rules
- Single non-vacuity example -> probabilistic coverage audit

---

## 5. Nueva Bibliografia Encontrada (Online Research)

### 5.1 AlphaEvolve (DeepMind, arXiv:2506.13131)

**Arquitectura**: Evolutionary loop con LLM ensemble (Gemini Flash for volume, Pro for quality). MAP-Elites + island-based populations. Diff-based mutations via EVOLVE blocks. Evaluation cascade (fast -> slow). Boltzmann-weighted parent selection.

**Resultados**: 4x4 complex matrix multiplication in 48 scalar multiplications (breaking Strassen). 0.7% recovery of Google's compute. 23% speedup in Gemini training.

**Mapping a SuperHash**:
| AlphaEvolve | SuperHash v2.0 |
|---|---|
| Program under evolution | Lean 4 PatternSoundRule instance |
| EVOLVE blocks | Pattern tree + proof body |
| LLM ensemble | Flash: pattern proposals; Pro: proof repair |
| Evaluation Stage 1 | `lake build` (binary soundness) |
| Evaluation Stage 2 | Pipeline Pareto improvement |
| Programs database | Pool of verified rules, MAP-Elites binned |
| Island model | Per CryptoConstruction: SPN, Feistel, Sponge, ARX |

### 5.2 AXLE MCP Server (Axiom, lean-4.28.0)

**14 tools** incluyendo repair_proofs, verify_proof, disprove, check, sorry2lemma. Integrable con Claude Code via:
```bash
claude mcp add axle -s user -e AXLE_DEFAULT_ENVIRONMENT=lean-4.28.0 -- python /path/to/axle-mcp/server.py
```

**Pipeline**: disprove (filter bad rules) -> repair_proofs (auto-proof) -> verify_proof (validate)

**Reliability estimate**: Trivial lemmas ~70-80%, medium ~10-20%, hard/custom ~0-5% (deterministic tactics, not neural prover).

### 5.3 CodeEvolve (open-source AlphaEvolve)

**Architecture**: Island-based GA + weighted LLM ensemble. Separate ensembles for exploration (Llama-3.1-8B) and exploitation (Qwen3-Coder-30B). MAP-Elites quality-diversity archive. Sandboxed evaluator.

**Evolution operators**: Depth exploitation, meta-prompting exploration, inspiration-based crossover (semantic, not syntactic).

**Key finding**: Open-weight models match closed-source at ~10% of API cost. Modular orchestration > raw model scale.

### 5.4 LGuess: LLM-Guided Equality Saturation

LLM proposes high-level rewrite checkpoints; e-graphs supply low-level rewrite chains between checkpoints. Solved 255/320 tasks vs DirectES's 204. Directly transferable: LLM proposes target crypto constructions, e-graph searches for rewrite paths.

### 5.5 DeepSeek-Prover-V2 (open-source, 671B)

88.9% miniF2F, 49/658 PutnamBench. Subgoal decomposition via sorry placeholders + GRPO (binary Lean feedback). Available on HuggingFace. Two sizes: 7B (32K context) and 671B.

### 5.6 Seed-Prover 1.5 (ByteDance)

88% PutnamBench, 5/6 IMO 2025. Agentic architecture using Lean as tool. Iterative refinement based on Lean feedback + proved lemmas.

### 5.7 AlphaVerus: Treefinement with Compiler Errors

Self-improving framework: Exploration -> Treefinement (tree search using verifier errors) -> Critique. 38% success on HumanEval-Verified. Key: compiler errors guide next attempt. Directly applicable to Lean rule generation.

### 5.8 egglog + Enumo/Chompy

**egglog**: Unifies Datalog + equality saturation. Merge functions for multi-objective aggregation. Faster than egg.

**Enumo** (OOPSLA 2023): DSL for programmable theory exploration. `candidates_by_diff` discovers rules from merged e-classes. Better rulesets than Ruler.

**Chompy**: Extends Enumo to conditional rewrite rules -- directly relevant for crypto rules with security parameter constraints.

### 5.9 SmoothE (ASPLOS 2025 Best Paper)

Differentiable e-graph extraction via gradient descent. GPU-accelerated. 8x-37x speedup over ILP. Supports **non-linear cost functions** -- critical for SuperHash's multiplicative security metrics.

### 5.10 SSD/Saguaro (ICLR 2026)

Speculative speculative decoding: 2x over SD, 5x over autoregressive. Lossless. Relevant only when LLM inference dominates (currently Lean compilation bottleneck dominates). **Deferred** until proven needed by profiling.

### 5.11 Concrete Semantics Infrastructure

- **BitVec** (Lean 4 core, no Mathlib): n-bit bitvectors with bv_decide tactic (SAT-based proofs via CaDiCaL)
- **GaloisField** (Mathlib): `GaloisField p n` for finite field formalization
- **grind tactic** (Lean 4.22+): SMT-style reasoning with Grobner basis solver
- **Colored e-graphs**: Conditional rewriting with context annotations

---

## 6. Insights de Nueva Bibliografia

### Insight 1: ASPEN validates the SuperHash architecture

ASPEN (Cornell/NVIDIA 2025) demonstrates LLM-guided e-graph rewriting works in production. 3 agents (rule proposal, selection, PPA feedback) = 16.51% area improvement. Directly transferable to crypto design space.

### Insight 2: Three-layer proving pipeline for sorry closure

AXLE (fast filter, ~30-40%) -> DeepSeek-Prover-V2 (medium-hard, +20-30%) -> Fine-tuned ReProver (domain-specific, +10-20%). Expected cumulative coverage: 60-70% automatic sorry closure.

### Insight 3: CodeEvolve provides ready-made orchestration

Island GA + LLM ensemble + MAP-Elites + sandboxed evaluation -- all open-source. Only need Lean evaluator plugin + rule DSL. Estimated effort: 3-4 weeks.

### Insight 4: Enumo/Chompy for automatic rule discovery

Enumo discovers better rulesets than Ruler (5.8x smaller, 25x faster). Chompy adds conditional rules. Seed with v1.0's 10 rules, let Enumo discover equivalences between crypto constructions.

### Insight 5: SmoothE solves non-linear Pareto extraction

v1.0's scalarization finds only convex hull. SmoothE supports non-linear cost functions (degree products, branch number products) with GPU acceleration. 8x-37x speedup over ILP.

### Insight 6: BitVec + bv_decide enables concrete semantics without Mathlib

BitVec built into Lean 4 core. bv_decide reduces goals to SAT, checked by CaDiCaL with LRAT certificate. Already used for AWS LNSym crypto verification. Sufficient for S-box concrete evaluation.

### Insight 7: E-graph children ARE recursive structure

No need for recursive CryptoDesign inductive type. Extend CryptoOp with hierarchical block constructors (spnBlock, feistelBlock, spongeBlock, arxBlock). E-graph naturally represents `Compose(SPN(...), Feistel(...))` via e-class references.

### Insight 8: RLVF reward should be multi-level

1. Level 0: Lean file parses (syntax)
2. Level 1: `lake build` succeeds with no sorry (compilation)
3. Level 2: `spec_audit.py` passes T1 (non-vacuity)
4. Level 3: Rule improves e-graph exploration (utility)

### Insight 9: AlphaVerus treefinement recovers ~38% of near-miss candidates

When candidate rule fails compilation, parse error -> feed to LLM -> refined version. Up to 3 attempts. Converts near-misses into valid rules.

### Insight 10: Lean compilation is the bottleneck, not LLM inference

At 5-30 seconds per compilation, throughput is ~50-100 evaluations/hour with 8 workers. Mitigations: olean caching, incremental compilation, rule template pre-compilation, fast syntax pre-check.

---

## 7. Sintesis de Insights

### Hallazgos Clave (Top 10)

1. **ASPEN validates architecture**: LLM-guided e-graph rewriting works (16% area improvement). 3-agent pattern directly transferable.
2. **Three-layer proving**: AXLE + DeepSeek-Prover + fine-tuned model = 60-70% automatic sorry closure.
3. **CodeEvolve ready**: Open-source island GA + LLM ensemble. Only need Lean evaluator plugin.
4. **Enumo/Chompy**: Automatic rule discovery supersedes manual enumeration.
5. **SmoothE**: Non-linear multi-objective extraction (ASPLOS 2025 Best Paper).
6. **BitVec concrete semantics**: No Mathlib needed for S-box verification.
7. **E-graph = recursive structure**: Add block constructors, not recursive types.
8. **Multi-level RLVF rewards**: parse -> compile -> non-vacuity -> utility.
9. **AlphaVerus treefinement**: ~38% recovery of near-miss candidates.
10. **Lean compilation bottleneck**: olean caching + incremental builds critical.

### Riesgos

| Riesgo | Nivel | Mitigacion |
|--------|-------|-----------|
| LLM genera reglas unsound | ALTO | Binary Lean kernel verification |
| Lean compilation latency (5-30s) | ALTO | olean caching, incremental compilation |
| LLM proof quality for custom defs | ALTO | Three-layer proving pipeline |
| E-graph explosion with many rules | MEDIO | Rule selection agent + fuel limit |
| RLVF reward hacking | MEDIO | Non-vacuity checks + spec_audit |
| Mathlib dependency for GaloisField | BAJO | BitVec sufficient for Phase 1 |

### Recomendaciones para Planificacion

1. **Phase 1 completion**: Extend CryptoOp with block constructors + bridge theorems
2. **Phase 2**: Rule discovery via CodeEvolve + Lean evaluator; AXLE for fast verification
3. **Phase 3**: RLVF loop with multi-level rewards; DeepSeek-Prover for proof generation
4. **Phase 4**: Autonomous design loop (discover -> saturate -> extract -> evaluate -> expand)
5. **Phase 5**: Concrete semantics via BitVec + bv_decide

### Recursos Prioritarios

1. **CodeEvolve** (github.com/inter-co/science-codeevolve) -- orchestration framework
2. **AXLE MCP** (axle.axiommath.ai) -- proof engineering tools
3. **DeepSeek-Prover-V2** (huggingface.co/deepseek-ai) -- proof generation
4. **Enumo** (github.com/ninehusky/enumo) -- rule discovery
5. **SmoothE** (ASPLOS 2025) -- differentiable extraction

---

## 8. Codigo Reutilizable de Proyectos Internos

### Matriz de Reutilizacion

| Componente SuperHash v2.0 | OptiSat | VR1CS | SuperTensor | LeanHash |
|---------------------------|---------|-------|-------------|----------|
| E-graph engine | EGraphState | EGraph/Core | EGraph (Op) | -- |
| Rewrite rules | SoundRewriteRule | 101 rules | SoundTensorRule | -- |
| Extraction | Triple (greedy/ILP/DP) | ILP encode | ILP certificate | -- |
| Pipeline soundness | full_pipeline_soundness | pipeline_e2e_sound | SemanticPreservation | -- |
| Cost models | -- | R1CSCostModel | TensorCostModel | -- |
| Crypto metrics | -- | pow5_identity | -- | SboxProperties, SPNDegree |
| Design params | -- | -- | -- | DesignSpace (12 thms) |

### Prioridad de Adaptacion

**Directamente copiable**: ENodeOps typeclass (SuperTensor), EGraph (Op) engine, SemanticPreservation
**Adaptar**: SoundRewriteRule -> SoundCryptoRule, TensorExpr -> CryptoDesign, R1CSCostModel -> CryptoCostModel
**Inspiracion**: Two-level compilation (SuperTensor), trust boundary (VR1CS), pipeline compositional (OptiSat)

---

## 9. Teoremas Formalizados (LeanHash/DesignSpace.lean)

### Resumen

| Metrica | Valor |
|---------|-------|
| Archivo | `LeanHash/DesignSpace.lean` |
| Toolchain | Lean 4.16.0 (sin Mathlib) |
| Definiciones | 8 (1 inductive, 3 structures, 4 defs) |
| Teoremas | 12 (todos probados, 0 sorry) |
| Non-vacuity examples | 3 |
| Instancias concretas | 2 (AES-128, Poseidon-128) |
| Build | PASS |

### Teoremas

1. `degree_mono_rounds` -- algebraic degree monotone in rounds
2. `active_sboxes_mono_rounds` -- active S-boxes monotone in rounds
3. `active_sboxes_mono_branch` -- active S-boxes monotone in branch number
4. `dominates_irrefl` -- Pareto dominance is irreflexive
5. `dominates_trans` -- Pareto dominance is transitive
6. `dominates_asymm` -- Pareto dominance is asymmetric
7. `compose_sound` -- rule composition preserves algebraic degree
8-12. Concrete instances (AES-128, Poseidon-128 algebraic degrees and S-box counts)

---

## 10. Libreria

- **Nombre**: LeanHash
- **Path**: `~/Documents/claudio/leanhash/`
- **Modulos**: 13 (12 existing + DesignSpace)
- **Teoremas totales**: ~146 (134 + 12)
- **Build**: OK
- **Uso**: Copiar/adaptar al proyecto SuperHash (NUNCA importar como dependencia)
