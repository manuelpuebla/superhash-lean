# Insights: SuperHash v3.1 — UHF Integration

**Fecha**: 2026-03-15
**Dominio**: lean4
**Estado del objeto**: upgrade (v3.0 → v3.1)

## 1. Análisis del Objeto de Estudio

SuperHash v3.1 integra hallazgos de 24 papers sobre funciones hash universales, grafos expansores y diseño criptográfico. La integración se realiza mediante 3 nuevos módulos en LeanHash (1,688 LOC, ~196 declaraciones, 0 sorry) que cubren 16 puntos de integración clasificados P0-P3.

**Estado actual (v3.0)**: 62 build jobs, ~17,500 LOC, 720 teoremas, 0 sorry, 15 rewrite rules (5 simplification + 10 expansion), 3 CryptoSemantics-proven rules.

**Keywords**: Carter-Wegman, Rogaway-Shrimpton hierarchy, ε-Almost Universal, UOWHF composition, expander graph hash, LP compression, DBL construction, ZesT hash, post-quantum, spectral gap, branch number bridge, multi-property preservation, short-output collision, dual universality, security profile.

## 2. Lecciones Aplicables

### Lecciones reutilizables
- **L-523 (Copy/Adapt Layer Strategy)**: v2.8 copió 3,476 LOC de LeanHash con ~1 bug/700 LOC. Copiar por tiers en orden topológico.
- **L-336 (Bridge Theorem Pattern)**: Conectar módulos vía bridge theorems unidireccionales (LeanHash → SuperHash), no bidireccionales.
- **L-513 (Compositional Pipeline Proofs)**: Monotonicity follows from additive fitness terms.
- **L-550 (safePow guard)**: 0^0=1 edge case in CryptoSemantics eval.

### Anti-patrones a evitar
- **Identity pass trap**: v3.0 discovered `roundCompose` UNSOUND for CryptoSemantics. Verify EVERY rule's direction.
- **Struct field explosion**: Do NOT add 8 fields to CryptoSemantics. Use separate SecurityProfile + bridge theorems.
- **Import hell**: Copy layer-by-layer, build after each tier. NEVER import LeanHash as lake dependency.
- **Unsupported constructor mapping**: Use `Option.none` for unsupported ops, not nonsense mappings.

### Técnicas reutilizables
- **Two-pass simp for PatternSoundRule**: (1) unfold Pattern.eval, (2) reduce decide + associativity lemmas.
- **Polymorphic eval extension**: New CryptoOp constructors get new `evalCryptoOpCS` clauses; old code unchanged.
- **Non-vacuity as deliverable**: Every theorem with ≥3 Prop hypotheses gets concrete `example`.

## 3. Bibliografía Existente Relevante

### Documentos clave (24 papers en uhf/)
| Paper | Relevancia | Módulo LeanHash |
|-------|-----------|-----------------|
| Carter & Wegman 1979 | Universal₂ definition, H₁/H₂/H₃ families | UniversalHashAdvanced |
| Rogaway & Shrimpton 2004 | 7 security notions, implications, separations | SecurityNotions |
| Naor & Yung 1991 | UOWHF composition preservation | SecurityNotions |
| Rogaway & Steinberger 2008 | LP231/352/362 compression bounds | ExpanderHash |
| Hirose 2006 | DBL construction, birthday bound improvement | ExpanderHash |
| Nguyen & Roscoe 2011 | Short-output collision 2^(1-b) | UniversalHashAdvanced |
| "New bounds for AU" | ε-AU key length lower bound | UniversalHashAdvanced |
| Tsurumaru & Hayashi 2012 | Dual universality, QKD applications | UniversalHashAdvanced |
| Charles, Goren, Lauter | Expander hash collision resistance (provable) | ExpanderHash |
| Petit 2009 (298pp thesis) | ZesT hash, LPS/Morgenstern attacks | ExpanderHash |
| Tillich & Zémor 2007 | LPS collision attack (anti-pattern) | ExpanderHash |
| Zhupa & Polak 2022 | Post-quantum DMAC from large-girth expanders | ExpanderHash |
| Caillat-Grenier 2024 | Spectral gap ↔ mixing rate, information theory | ExpanderHash |
| Preneel 1999 | Generic attack taxonomy (birthday, MITM, herding) | SecurityNotions |
| Al-Kuwari et al. 2011 | Multi-property preservation, wide pipe | SecurityNotions |

### Grafo de conceptos
- UHF → AU/AXU/ASU extensions → Privacy Amplification (LHL)
- Expander Graphs → LPS/Morgenstern/Zémor-Tillich/Pizer/ZesT
- Compression Function → LP Compression / Davies-Meyer / DBL
- Collision Resistance ← MD Transform ← Sponge ← Iterated Hash

### Gaps identificados
- No hay papers sobre verificación formal de UHF en proof assistants (SuperHash sería el primero)
- Falta combinación UHF + expander graphs en un solo framework
- Quantum security de expander-based families solo parcialmente cubierta

## 4. Estrategias y Decisiones Previas

### Estrategias ganadoras
1. **Layer-based copy** (v2.8): 3,476 LOC copiados con 0 bugs. Copy por tiers DAG-ordered.
2. **Polymorphic eval extension** (v3.0): New constructors = new clauses in evalCryptoOpCS.
3. **Additive fitness terms** (v2.5→v2.6): New fitness components are additive, non-breaking.
4. **Unidirectional bridges** (v2.7): LeanHash → SuperHash only. No lifting back.

### Decisiones arquitecturales
- **NO importar LeanHash como dep lake** — copiar/adaptar (global rule)
- **NO extender CryptoOp inductive** — use polymorphic eval + new clauses
- **NO añadir campos a CryptoSemantics** — usar SecurityProfile separado + bridges
- **Saturation en CryptoSemantics, extraction en Nat** — two-level pipeline

### Benchmarks de referencia
| Métrica | v2.8 | v3.0 | v3.1 (target) |
|---------|------|------|--------------|
| Build jobs | 52 | 62 | ~70 |
| LOC | ~15K | ~17.5K | ~20K |
| Theorems | ~600 | ~720 | ~850 |
| Sorry | 0 | 0 | 0 |
| Rewrite rules | 10 | 15 | 20+ |
| CS-proven rules | 1 | 3 | 5+ |

## 5. Nueva Bibliografía Encontrada

Sección omitida (--skip-online)

## 6. Insights de Nueva Bibliografía

Sección omitida (sin descargas nuevas)

## 7. Síntesis de Insights

### Hallazgos clave

1. **SecurityProfile es la mejora de mayor impacto** (P0). Pasar de `securityLevel : Nat` a un vector de 4 dimensiones (Coll, Pre, Sec, eSec) permite que el Pareto front optimice sobre múltiples nociones simultáneamente. LeanHash ya tiene las implicaciones probadas.

2. **UOWHF composition rule es directamente formalizable** (P0). `compose(f, g)` preserva target-collision-resistance — Naor-Yung 1991. Esto se convierte en PatternSoundRule: la composición en el E-graph preserva UOWHF automáticamente.

3. **Carter-Wegman H₁ universality es un constraint decidible** (P1). Para p≥m: `collisions * m ≤ p²` — verificable por `native_decide` para parámetros concretos. Enriquece `UHFConstraint.lean`.

4. **Short-output bound = 2^(1-b) cierra un gap en fitness** (P1). SuperHash no modela la relación output_length ↔ collision_probability. Con Nguyen-Roscoe: `truncation_collision_bound b : 2 ≤ 2^b` permite penalizar truncaciones.

5. **LP compression bounds dan security EXACTO** (P2). LP231: 50% of birthday, LP362: 63%. Esto permite al E-graph comparar diseños blockcipher-based con bounds precisos, no heurísticos.

6. **Branch number ↔ spectral gap bridge conecta SPN y expander** (P2/P3). `branchNumber ≥ 2 → spectralGap ≥ (bn-1)/degree`. Esto unifica wide trail strategy con teoría espectral de grafos.

7. **LPS hash es un anti-pattern documentado** (P2). Tillich-Zémor 2007 demostró collisions quasi-lineales. Si el E-graph genera diseños expander-based, debe excluir LPS puro.

8. **Post-quantum flag es simple de implementar** (P3). `quantumBits * 2 ≥ classicalBits` (Grover bound). Agregar como campo booleano a SecurityProfile.

### Riesgos identificados

1. **Struct explosion risk**: Adding fields to CryptoSemantics cascades through 400+ theorems. MITIGATE: Use separate SecurityProfile.
2. **CryptoOp constructor cascade**: New constructors require new evalCryptoOpCS clauses + wf proofs. MITIGATE: Add incrementally, 2-3 at a time.
3. **Heartbeat budget**: pipeline_soundness already at 8M. Each new component adds load. MITIGATE: Keep new proofs in separate files, not in pipeline chain.
4. **LeanHash 4.16 → SuperHash 4.28 API drift**: Some lemma names differ. MITIGATE: Known from v2.8 (1 bug/700 LOC rate).

### Recomendaciones para planificación

**Fase 1 (P0 — Security Model)**:
- Copy `SecurityNotions.lean` from LeanHash (adapt to 4.28)
- Create `Crypto/SecurityNotions.lean` in SuperHash with SecurityProfile
- Bridge: `CryptoSemantics → SecurityProfile` via computed fields
- Add UOWHF composition as PatternSoundRule

**Fase 2 (P1 — UHF Enhancement)**:
- Copy `UniversalHashAdvanced.lean` relevant parts
- Extend `UHFConstraint.lean` with Carter-Wegman H₁ verification
- Add ε-AU key length bound to fitness
- Add short-output collision bound

**Fase 3 (P2 — Design Space Expansion)**:
- Copy `ExpanderHash.lean` relevant parts
- Add LP compression parameters to design space (NOT as CryptoOp constructor — as cost model)
- Add DBL expansion rule to ExpansionRules.lean
- Add branch-spectral bridge theorem

**Fase 4 (P3 — Advanced Features)**:
- Add post-quantum flag to SecurityProfile
- Add spectral gap ↔ branch number connection
- Concrete examples: AES, Poseidon, ZesT security profiles

### Recursos prioritarios
1. LeanHash/SecurityNotions.lean — 57 declarations, security hierarchy
2. LeanHash/UniversalHashAdvanced.lean — 73 declarations, UHF families + composition
3. LeanHash/ExpanderHash.lean — 66 declarations, expander + LP + DBL
4. LeanHash/UniversalHash.lean — 0 sorry, LHL + extractor bounds
5. superhash_v3.1_background.md — 16 integration points with priority
