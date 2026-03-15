## Análisis: 24 Papers UHF × SuperHash v3.0

He indexado los 24 PDFs (total ~900 páginas) y los he cruzado con los 62 archivos de SuperHash. Organizo por **tiers de relevancia** para el proyecto.

---

### TIER 1: DIRECTAMENTE FORMALIZABLES — impacto inmediato en SuperHash

#### 1. Carter & Wegman — "Universal Classes of Hash Functions" (1979)
**Qué aporta**: El paper fundacional. Define Universal₂ con `P[h(x)=h(y)] ≤ 1/m` y tres familias concretas (H₁ mod-p, H₂ XOR, H₃ lineal). SuperHash ya usa la definición en `UHFConstraint.lean` pero solo tiene la cota `δ·2^l ≤ 2^n` de Tyagi-Watanabe.

**Cómo mejora SuperHash**: Formalizar las tres familias concretas como `ConcretUHF` instances. Esto permite que el E-graph **verifique** que una construcción generada ES universal₂, no solo que satisface la cota. Actualmente el fitness solo chequea bounds — con Carter-Wegman podríamos probar universality del diseño completo.

**Beneficio**: El E-graph podría tener una regla: "si el diseño es universal₂, collision_prob ≤ 1/2^l" como **constraint verificada**, no como heurística.

---

#### 2. Rogaway & Shrimpton — "Hash-Function Basics: Definitions, Implications, Separations" (2004)
**Qué aporta**: 7 nociones de seguridad formales (Coll, Sec, aSec, eSec, Pre, aPre, ePre) con una **matriz completa** de implicaciones y separaciones. SuperHash actualmente solo usa `collision_resistance` como noción monolítica.

**Cómo mejora SuperHash**: Refinar `SecurityMetrics` para distinguir entre las 7 nociones. Actualmente `securityLevel` es un solo Nat — con Rogaway-Shrimpton podríamos tener:
```
structure SecurityProfile where
  collisionBits : Nat       -- Coll
  preImageBits : Nat        -- Pre
  secondPreImageBits : Nat  -- Sec
  targetCRBits : Nat        -- eSec/aSec
```
Y probar las **implicaciones formales**: `Coll → Sec`, `Coll → eSec`, pero `¬(Sec → Coll)`.

**Beneficio**: El Pareto front podría optimizar sobre **múltiples nociones de seguridad** simultáneamente, no solo sobre un escalar. Un diseño podría ser óptimo para collision resistance pero débil para preimage — el E-graph lo detectaría.

---

#### 3. Naor & Yung — "Universal One-Way Hash Functions" (1991)
**Qué aporta**: UOWHF = target collision resistance (más débil que full CR). Prueba que UOWHF ⟺ OWF (existe si y solo si existen funciones one-way). La composición preserva UOWHF.

**Cómo mejora SuperHash**: Actualmente `UHFConstraint.lean` solo tiene la cota 2-UHF. UOWHF añade una jerarquía:
- Full CR: hard to find *any* collision
- UOWHF/TCR: hard to find collision *given random x*
- 2-UHF: probabilistic bound

SuperHash podría tener una **regla de reescritura verificada**: "composición de UOWHF preserva UOWHF" — esto es exactamente lo que `compose` hace en el E-graph, y Naor-Yung lo prueba formalmente.

**Beneficio**: Justificación formal de que `compose(f, g)` preserva target-collision-resistance. Directamente formalizable como PatternSoundRule sobre una noción más fuerte que collision probability.

---

#### 4. "New Bounds for Almost Universal Hash Functions"
**Qué aporta**: Cota combinatoria inferior para key length de ε-AU families. La cota es más tight que la de teoría de códigos (Singleton bound). Polynomial hashing alcanza la cota con igualdad. Efecto threshold de Wegman-Carter: para ε < 1/q, el key length escala como log(message length).

**Cómo mejora SuperHash**: `UHFConstraint.lean` actualmente verifica `δ·2^l ≤ 2^n` como condición binaria (sí/no). Con esta cota, podríamos computar el **key length mínimo** requerido para lograr ε-almost universality. Esto añadiría un campo a `CryptoSemantics`:
```
minKeyLength : Nat  -- bits de clave necesarios para ε-AU
```

**Beneficio**: El fitness function podría penalizar diseños que requieren claves demasiado largas para su nivel de universality. Constraint formal, no heurística.

---

#### 5. Nguyen & Roscoe — "Short-Output Universal Hash Functions" (2011)
**Qué aporta**: Función `digest()` con collision probability ε_c = 2^(1-b) para output de b bits. Superior a MMH y NH (usados en UMAC). Análisis de operaciones por bit de input.

**Cómo mejora SuperHash**: El campo `gateCount` en CryptoSemantics es actualmente genérico. Con Nguyen-Roscoe podríamos tener una cota formal: para output de b bits, la collision probability es exactamente 2^(1-b), con costo de O(n) multiplicaciones.

**Beneficio**: Permite al E-graph evaluar **short-output hashes** (truncaciones) con bounds formales. Actualmente SuperHash no modela la relación entre output length y collision probability — esta es exactamente esa relación.

---

### TIER 2: NUEVOS PARADIGMAS DE DISEÑO — amplían el espacio de exploración del E-graph

#### 6. Charles, Goren & Lauter — "Cryptographic Hash Functions from Expander Graphs"
**Qué aporta**: Hash functions con **collision resistance provable** basada en hardness de isogeny computation. Dos familias: LPS (matrices en PSL(2,Fp)) y Pizer (supersingular elliptic curves). Provablemente collision-resistant.

**Cómo mejora SuperHash**: Esto es un **paradigma completamente nuevo** que SuperHash no tiene. Los 12 CryptoOp actuales son todos SPN/Feistel/Sponge — no hay grafos expansores. Se podrían agregar:
```
| .expanderWalk (graph : ExpanderType) (steps : Nat) (c : EClassId) -- Caminata en grafo expansor
| .cayleyHash (group : GroupType) (generators : Nat) (c : EClassId) -- Hash de Cayley
```

**Beneficio**: El E-graph podría explorar diseños que **combinan** SPN rounds con expander walks — algo que ningún diseñador humano ha hecho. La collision resistance del componente expander es provable (no heurística).

---

#### 7. Rogaway & Steinberger — "Hash Functions from Fixed-Key Blockciphers" (2008)
**Qué aporta**: Familia LP de compression functions con security bounds exactos:
- LP231: 2n→n con 3 calls, collision ≈ N^0.5
- LP352: 3n→2n con 5 calls, collision ≥ N^0.55
- LP362: 3n→2n con 6 calls, collision ≥ N^0.63

Análisis automatizado de seguridad usando sistemas lineales.

**Cómo mejora SuperHash**: SuperHash ya tiene `spnBlock` y `feistelBlock` como constructores. Las familias LP son un tercer paradigma de construcción: **multiple blockcipher calls** con XOR combinations. Se podría agregar:
```
| .lpCompress (calls : Nat) (inputBlocks : Nat) (outputBlocks : Nat) -- Familia LP
```
Con las cotas de seguridad directamente formalizadas como parte de `evalCryptoOpCS`.

**Beneficio**: Security bounds **exactos** (no heurísticos) para compresiones blockcipher-based. El E-graph podría explorar LP231 vs LP362 vs SPN y comparar security/cost.

---

#### 8. Hirose — "How to Construct Double-Block-Length Hash Functions" (2006)
**Qué aporta**: Constructions para compression 2n-bit usando componentes n-bit con security O(q²/2^n). Noción de indistinguishability in the iteration.

**Cómo mejora SuperHash**: `compose` en SuperHash multiplica grados algebraicos. Una DBL construction combinaría dos `compose` con diferentes keys para producir output de longitud doble. Esto es exactamente lo que `roundSplitRule` hace al revés — DBL es la operación inversa.

**Beneficio**: Regla de expansión: `hash(2n, x) → dbl(hash(n, x₁), hash(n, x₂))` con security bound formal.

---

#### 9. Zhupa & Polak — "Keyed Hash Function from Large Girth Expander Graphs" (2022)
**Qué aporta**: DMAC construction con collision resistance basada en cycle-finding hardness en grafos D(n,q). Post-quantum secure. ~4 field operations per input bit.

**Cómo mejora SuperHash**: Este es el paper más reciente (2022) y el más relevante para **post-quantum hash design**. El gateCount de 4 operaciones/bit es competitivo con SPN. La propiedad post-quantum es crucial — SuperHash actualmente no modela seguridad post-quantum.

**Beneficio**: Podría agregar un campo `postQuantumSecure : Bool` a SecurityMetrics y un constructor `expanderMAC` al E-graph.

---

### TIER 3: FUNDAMENTOS TEÓRICOS — fortalecen las pruebas existentes

#### 10. Tsurumaru & Hayashi — "Dual Universality" (2012)
**Qué aporta**: ε-almost dual universal₂ generaliza universal₂. Correspondencia 1-1 con códigos. Aplicaciones a QKD y privacy amplification.

**Relevancia**: Conecta directamente con `SourceEntropy.lean` (privacy amplification = extracción de entropía). La dual universality podría dar bounds más tight para el LHL.

#### 11. Caillat-Grenier — "Expander Graphs and Information-Theoretic Cryptography" (2024, thesis)
**Qué aporta**: Spectral bounds + Kolmogorov complexity para secret key agreement. Alon-Boppana bounds. Expander mixing lemma.

**Relevancia**: El spectral gap de grafos expansores determina la tasa de mezcla — esto es directamente análogo al branch number en SPN. Podría formalizarse como: `spectralGap(G) ≥ branchNumber(L) - 1` para conectar las dos teorías.

#### 12. Preneel — "The State of Cryptographic Hash Functions" (1999)
**Qué aporta**: Survey completo: OWHF, CRHF, UOWHF, ε-AU, ε-ASU. Ataques genéricos (birthday, meet-in-middle, fixed-point). Comparación MDC-2/MDC-4.

**Relevancia**: Taxonomía de ataques que SuperHash debería modelar. Actualmente el fitness solo considera birthday + differential + algebraic. Preneel documenta 6+ ataques adicionales (meet-in-middle, fixed-point, herding).

#### 13. Al-Kuwari et al. — "Recent Design Trends and Security Notions" (2011)
**Qué aporta**: Multi-Property-Preserving (MPP) constructions, wide/double pipe, sponge analysis.

**Relevancia**: MPP es exactamente lo que SuperHash necesita para `pipeline_soundness_crypto` — probar que la saturación preserva MÚLTIPLES propiedades de seguridad simultáneamente.

---

### TIER 4: CONTEXTO Y ATAQUES — informan decisiones de diseño

#### 14. Tillich & Zémor — "Collisions for the LPS Hash" (2007)
**Qué aporta**: Ataque quasi-linear a LPS usando Gaussian integers. Collision encontrada para primos de 100 dígitos.

**Relevancia**: **Anti-pattern** — si SuperHash genera diseños basados en LPS, este paper demuestra que son atacables. El E-graph debería tener una constraint que excluya LPS puro.

#### 15. Petit — "On Graph-Based Cryptographic Hash Functions" (2009, thesis 298pp)
**Qué aporta**: Análisis exhaustivo de LPS, Morgenstern, Zémor-Tillich. Propone ZesT (no-malleable). Ataques de colisión y preimage para cada variante.

**Relevancia**: El atlas más completo de ataques a hash functions basadas en grafos. Si SuperHash incorpora expander hashes, este es el manual de lo que funciona y lo que no.

#### 16. Petit — "On Expander Hash Functions" (2009, thesis 124pp)
**Qué aporta**: ZesT hash con collision resistance provable + parallelism + non-malleability.

**Relevancia**: ZesT es la **mejor variante** de expander hash (corrige LPS y Morgenstern). Si se agrega un constructor expander al E-graph, debería ser ZesT, no LPS.

---

### Plan de Integración Concreto

Basado en el análisis, las mejoras de mayor impacto para SuperHash son:

| Prioridad | Acción | Papers | Módulo SuperHash |
|-----------|--------|--------|-----------------|
| **P0** | Formalizar 7 nociones de seguridad Rogaway-Shrimpton | #2 | `Crypto/SecurityNotions.lean` (nuevo) |
| **P0** | Composición preserva UOWHF (regla de reescritura) | #3 | `Rules/CryptoRulesCS.lean` |
| **P1** | Familias concretas Universal₂ (Carter-Wegman H₁,H₂,H₃) | #1 | `Crypto/UHFConstraint.lean` |
| **P1** | Cota ε-AU para key length mínimo | #4 | `Crypto/UHFConstraint.lean` |
| **P1** | Collision prob = 2^(1-b) para short-output | #5 | `Crypto/Fitness.lean` |
| **P2** | Constructor expanderHash en CryptoOp | #6, #15, #16 | `CryptoOp.lean` + `CryptoNodeOps.lean` |
| **P2** | Familia LP de compression functions | #7 | `CryptoOp.lean` + rewrite rules |
| **P2** | Double-block-length expansion rule | #8 | `Rules/ExpansionRules.lean` |
| **P3** | Modelo post-quantum (expander MACs) | #9 | `Crypto/Semantics.lean` |
| **P3** | Dual universality para LHL bounds | #10 | `Crypto/SourceEntropy.lean` |
| **P3** | Spectral gap ↔ branch number bridge | #11 | `Bridge/` (nuevo) |
