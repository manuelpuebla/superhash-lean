# SuperHash — Análisis de PDFs "Asymptotic AG" para Diseño Hash Quantum-Resistant

**Fecha**: 2026-03-15
**Fuente**: 16 PDFs en `~/Downloads/Asymptotic AG/` (indexados en `biblioteca/asymptotic-ag/`)
**Proyecto**: SuperHash v3.2 (~800 teoremas, 67 archivos Lean, 0 sorry)

---

## Contexto de SuperHash

SuperHash v3.2 es un framework de diseño automático de hashes con verificación formal en Lean 4. Ya tiene:
- **E-graph engine** con equality saturation + extraction Pareto
- **CryptoSemantics** (7 métricas: algebraicDegree, differentialUniformity, linearBias, branchNumber, activeMinSboxes, latency, gateCount)
- **Security model**: birthday bound, LHL extractors, algebraic security, Boura-Canteaut
- **Expander graph bounds** (LP, DBL, ZesT) con un bound post-quantum básico: `quantumBits * 2 ≥ classicalBits` (Grover)
- **UHF theory** (Carter-Wegman, ε-AU, dual universality)
- 24 papers de UHF/expander ya integrados

### El gap cuántico actual

SuperHash maneja la seguridad post-cuántica con una única regla naive: **halving de Grover** (`q-bits = c-bits / 2`). Esto es insuficiente para:
1. Ataques algebraicos cuánticos (no solo fuerza bruta)
2. Hash families donde la reducción de seguridad depende de la estructura algebraica
3. Parametrización óptima de hashes basados en códigos/curvas

**Bounds existentes en `Security/QuantumBounds.lean`:**
- `groverPreimageFloor(n) = n/2`
- `bhtCollisionFloor(n) = n/3`
- `quantum_floor_le_classical` theorem

**Bounds existentes en `Crypto/ExpanderBounds.lean`:**
- Zhupa-Polak (post-quantum expander)
- Charles-Goren-Lauter (isogenías)

---

## Clasificación por Relevancia

### TIER 1 — Directamente Aplicables (incorporar en próxima fase)

#### 1. "Asymptotic Bounds on Quantum Codes from AG Codes" (Feng, Ling, Xing 2006)
**Relevancia: MAXIMA**

Este paper establece la conexión fundamental: **códigos AG → códigos cuánticos buenos asintóticamente**. La conexión con SuperHash es directa por la dualidad códigos-hashes (via LHL, ya formalizada en SuperHash):

- **Teorema central**: α_q(δ) ≥ A(q) - δ, donde A(q) es la constante de Drinfeld-Vladut. Esto da un bound asintótico para tasa cuántica vs distancia.
- **Aplicación a SuperHash**: Un hash basado en un código AG con distancia d tiene seguridad cuántica directamente acotada por esta fórmula. Supera el naive Grover halving porque:
  - Para códigos AG sobre F_q² con q² ≥ 49, el bound mejora al quantum GV bound
  - La mejora viene de códigos **no-lineales** clásicos convertidos a cuánticos (Proposición 2.4)
- **Formalización**: Nuevo módulo `SuperHash/Crypto/QuantumAGBound.lean`:
  - `def quantumAGBound (q delta : Nat) : Nat` — bound asintótico
  - `theorem quantumAG_improves_grover` — demuestra que para ciertos parámetros, AG > Grover/2
  - Integrar como campo adicional en `SecurityProfile`

#### 2. "Asymptotically Good Generalized AG Codes" (Chang 2010)
**Relevancia: MUY ALTA**

La tesis construye familias de códigos asintóticamente buenos via **torres de extensiones Artin-Schreier**. Estas torres son la fuente de hashes con parámetros escalables:

- **Construcción clave**: Torres F₀ ⊂ F₁ ⊂ F₂ ⊂ ... con N(Fᵢ)/g(Fᵢ) → A(q) (ratio optimal de puntos racionales a género)
- **GAG codes** generalizan Goppa y Reed-Solomon — permiten hashes con flexibilidad paramétrica superior
- **Aplicación a SuperHash**: Nuevo constructor en CryptoOp:
  ```
  | agCodeHash (genus fieldSize numPoints : Nat) (rounds : Nat)
  ```
  Con semántica CryptoSemantics donde:
  - `algebraicDegree` viene del genus
  - `differentialUniformity` viene de la distancia del código dual
  - Security bound = A(q) - δ (del paper de Feng-Ling-Xing)
- **Bridge theorem**: `agCodeHash_security_ge_grover` — la seguridad AG es al menos tan buena como Grover, y estrictamente mejor para q² ≥ 49

#### 3. "Asymptotic Methods in Number Theory and AG" (Lebacque & Zykin 2011)
**Relevancia: ALTA**

Survey que unifica la teoría asintótica de campos globales. Proporciona:

- **Invariantes de Tsfasman-Vladut**: Marco para medir qué tan "buenos" son los parámetros de un código/hash asintóticamente
- **Desigualdad de Drinfeld-Vladut**: A(q) ≤ √q - 1 (bound superior tight sobre F_q²)
- **Curvas modulares y de Shimura**: Fuentes de curvas con muchos puntos → mejores hashes
- **Aplicación a SuperHash**: Formalizar `A(q)` como constante y las desigualdades básicas. Esto fundamenta rigurosamente los bounds del paper 1 (Feng et al.) y da un framework para parametrizar hashes óptimamente.

---

### TIER 2 — Framework Teórico para Pruebas de Seguridad

#### 4. "The Polynomial Method over Varieties" (Walsh 2020)
**Relevancia: MEDIA-ALTA**

Herramientas para analizar la estructura algebraica de variedades → probar que los outputs de hash están bien distribuidos:

- **Polynomial partitioning para variedades**: Si los outputs del hash viven en una variedad de grado bajo, la función es insegura. El método polinomial da bounds sharp para detectar esta concentración.
- **Aplicación**: Formalizar `algebraicConcentrationBound` — si degree(collision variety) > threshold, el hash es seguro contra ataques algebraicos. Esto complementa el `algebraicSecurityBits` existente con bounds geométricos.

#### 5. "Inverse Sieve Problems" (Walsh 2011/2013 + Menconi, Paredes, Sasyk 2020)
**Relevancia: MEDIA-ALTA** (3 papers, misma línea)

El **contrapositivo** del problema inverso del tamiz da garantías de distribución:

- Si un set S ocupa pocas clases residuales mod p → S es algebraico (está en Z(f))
- **Contrapositivo**: Si diseñamos el hash para que NO sea algebraico → outputs bien distribuidos mod p para todo p
- **Paper de Menconi-Paredes-Sasyk**: Extiende a variedades sobre campos globales — exactamente el setting de hashes sobre campos finitos
- **Aplicación a SuperHash**: Nuevo test de seguridad `distributionModPrimesCheck` que verifica que los outputs del hash no se concentran en pocas clases residuales. Si pasa → bound formal de seguridad.

#### 6. "Effective Hilbert's Irreducibility Theorem" (Paredes & Sasyk 2022)
**Relevancia: MEDIA**

Cuando construyes familias hash parametrizadas por polinomios, Hilbert's Irreducibility garantiza que "casi todas" las especializaciones dan instancias seguras:

- **Bounds explícitos**: Para F(T,Y) ∈ K[T,Y], el número de t ∈ O_K con ||t|| ≤ B que destruyen irreducibilidad es O(B^{1-1/d})
- **Aplicación**: Si SuperHash genera un diseño hash parametrizado, este teorema garantiza que la fracción de parámetros "malos" (que dan hashes débiles) es asintóticamente despreciable. Formalizable como `parameterSafetyBound`.

#### 7. "Uniform Bounds for Rational Points" (Paredes & Sasyk 2021)
**Relevancia: MEDIA**

Bounds uniformes sobre puntos racionales en variedades → bounds sobre colisiones:

- **Aplicación**: La "variedad de colisiones" {(x,x') : h(x)=h(x')} es una variedad algebraica. Bounds uniformes sobre sus puntos racionales → bounds de collision resistance. Complementa el birthday bound con bounds algebraicos.

---

### TIER 3 — Conexiones Tangenciales

| Paper | Conexión | Aplicabilidad |
|-------|----------|---------------|
| Local Uniformity (Walsh 2021) | Funciones multiplicativas → familias hash multiplicativas | BAJA — SuperHash no usa hashes multiplicativos puros |
| Phase Relations (Walsh 2023) | Fourier uniformity → pseudorandomness de hashes | BAJA — más teórico que aplicable |
| Stability under Scaling (Walsh 2023) | Misma línea que Phase Relations | BAJA |
| Asymptotic Algebraic Combinatorics (2019) | Young tableaux, Schubert — sin conexión directa | MUY BAJA |
| Asymptotic Differential Algebra (2003) | H-fields, valuaciones — tangencial | MUY BAJA |
| Asymptotic Geometry of Polynomials (slides) | Zeros de polinomios random — tangencial | MUY BAJA |
| Quantized Barycenters of Polytopes (2024) | Toric varieties, Ehrhart — sin conexión | MUY BAJA |

---

## Estrategia de Incorporación a SuperHash

### Estrategia A: AG Code Hash Families (Papers 1 + 2 + 3)

```
Nuevo módulo: SuperHash/Crypto/QuantumAG/
├── AGBounds.lean        -- A(q), Drinfeld-Vladut, quantumAGBound
├── TowerParams.lean     -- Parámetros de torres Artin-Schreier
├── AGHashSecurity.lean  -- Reduction: AG distance → hash collision bound
└── QuantumBridge.lean   -- Bridge: quantumAGBound ≥ groverBound para q² ≥ 49
```

**Teorema clave a formalizar**:
```lean
theorem agHash_quantum_security :
  ∀ (q : Nat) (hq : q ≥ 7) (delta : Nat) (hd : delta > 0),
  quantumAGBound q delta ≥ groverBound (agClassicalBound q delta)
```

Esto probaría formalmente que los hashes basados en códigos AG sobre F_{q²} con q ≥ 7 tienen seguridad cuántica superior al naive Grover halving.

### Estrategia B: Distribution Bounds via Inverse Sieve (Papers 4 + 5 + 6 + 7)

```
Nuevo módulo: SuperHash/Crypto/Distribution/
├── InverseSieve.lean    -- Si outputs son algebraicos → concentrados → inseguro
├── PolyMethod.lean      -- Algebraic concentration bounds
└── DistributionTest.lean -- Tests verificados de distribución mod primes
```

Esto extendería el modelo de seguridad de SuperHash más allá de las 7 métricas CryptoSemantics actuales, agregando una **8va dimensión**: distribución algebraica.

### Estrategia C: Parametrización Optimal de Hashes (Papers 3 + 6)

Los invariantes de Tsfasman-Vladut + Hilbert's Irreducibility dan un framework para elegir parámetros óptimos:
- Para cada `CryptoOp`, cuál es el campo finito óptimo F_q
- Para hashes expandereros (ya en SuperHash), cuál es el genus óptimo
- Bounds explícitos de "parámetros seguros" vs "parámetros malos"

---

## Recomendación Priorizada

**Incorporar en este orden:**

1. **Feng-Ling-Xing (2006)** — Bound cuántico AG. Impacto inmediato: supera el naive Grover en `ExpanderBounds.lean`. Es un paper de 7 páginas con resultados formalizables directamente.

2. **Chang (2010)** — Torres Artin-Schreier. Proporciona la maquinaria constructiva para definir familias hash AG. Sin esto, el bound de Feng et al. es teórico; con esto, se pueden instanciar hashes concretos.

3. **Lebacque-Zykin (2011)** — Formalizar A(q) y Drinfeld-Vladut como constantes del framework. Fundamenta los dos anteriores.

4. **Walsh (polynomial method) + Menconi-Paredes-Sasyk (inverse sieve)** — Distribution bounds como 8va dimensión de seguridad. Más ambicioso pero de alto valor.

Los 9 papers restantes son de valor contextual o tangencial para SuperHash.

---

## Resumen Ejecutivo

| Prioridad | Paper | Impacto en SuperHash |
|-----------|-------|---------------------|
| **1** | Feng-Ling-Xing (2006) — Quantum AG bounds | Superar naive Grover con α_q(δ) ≥ A(q) - δ |
| **2** | Chang (2010) — Torres Artin-Schreier | Constructor `agCodeHash` con parámetros escalables |
| **3** | Lebacque-Zykin (2011) — Asymptotics survey | Formalizar A(q) y Drinfeld-Vladut como framework |
| **4** | Walsh (2020) + Menconi et al. (2020) | 8va dimensión de seguridad: distribución algebraica |
| **5** | Paredes-Sasyk (2021/2022) | Bounds de colisión algebraicos + parametrización |
| 6-16 | Resto | Tangencial para hash design |

**Los 5 papers prioritarios** podrían constituir una **Fase 4 de SuperHash** enfocada en seguridad cuántica algebraico-geométrica, superando significativamente el modelo actual de "Grover divide por 2".
