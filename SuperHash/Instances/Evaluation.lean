import SuperHash.Pipeline.Integration

/-!
# SuperHash.Instances.Evaluation — Concrete pipeline evaluation

Provides:
- `designToEGraph`: converts a CryptoExpr to an E-graph with a root node
- `#eval` smoke tests with AES-like and Poseidon-like designs
- End-to-end pipeline execution demonstrations
-/

namespace SuperHash

-- ══════════════════════════════════════════════════════════════════
-- Section 1: CryptoExpr → EGraph conversion
-- ══════════════════════════════════════════════════════════════════

/-- Convert a CryptoExpr into an E-graph, returning (rootId, graph).
    Recursively adds all sub-expressions as E-graph nodes. -/
def designToEGraph : CryptoExpr → EGraph CryptoOp → (EClassId × EGraph CryptoOp)
  | .const val, g => g.add ⟨.const val⟩
  | .var id, g => g.add ⟨.const id⟩  -- variables become const nodes
  | .sbox d child, g =>
    let (childId, g) := designToEGraph child g
    g.add ⟨.sbox d childId⟩
  | .linear b child, g =>
    let (childId, g) := designToEGraph child g
    g.add ⟨.linear b childId⟩
  | .xor l r, g =>
    let (lId, g) := designToEGraph l g
    let (rId, g) := designToEGraph r g
    g.add ⟨.xor lId rId⟩
  | .round d b child, g =>
    let (childId, g) := designToEGraph child g
    g.add ⟨.round d b childId⟩
  | .compose f s, g =>
    let (fId, g) := designToEGraph f g
    let (sId, g) := designToEGraph s g
    g.add ⟨.compose fId sId⟩
  | .parallel l r, g =>
    let (lId, g) := designToEGraph l g
    let (rId, g) := designToEGraph r g
    g.add ⟨.parallel lId rId⟩
  | .iterate n body, g =>
    let (bodyId, g) := designToEGraph body g
    g.add ⟨.iterate n bodyId⟩
  | .spnBlock r s l, g =>
    let (sId, g) := designToEGraph s g
    let (lId, g) := designToEGraph l g
    g.add ⟨.spnBlock r sId lId⟩
  | .feistelBlock r f, g =>
    let (fId, g) := designToEGraph f g
    g.add ⟨.feistelBlock r fId⟩
  | .spongeBlock rt cap p, g =>
    let (pId, g) := designToEGraph p g
    g.add ⟨.spongeBlock rt cap pId⟩
  | .arxBlock r a rot x, g =>
    let (aId, g) := designToEGraph a g
    let (rotId, g) := designToEGraph rot g
    let (xId, g) := designToEGraph x g
    g.add ⟨.arxBlock r aId rotId xId⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Concrete designs
-- ══════════════════════════════════════════════════════════════════

/-- AES-like design: 10 rounds of (sbox-7 ∘ linear-5). -/
def aesLikeDesign : CryptoExpr :=
  .iterate 10 (.compose (.sbox 7 (.const 0)) (.linear 5 (.const 0)))

/-- Poseidon-like design: 8 rounds of round(5, 3, x). -/
def poseidonLikeDesign : CryptoExpr :=
  .iterate 8 (.round 5 3 (.const 0))

/-- Simple SPN design: sbox + linear. -/
def simpleSPN : CryptoExpr :=
  .compose (.sbox 7 (.const 0)) (.linear 5 (.const 0))

/-- Feistel-like design: xor of two branches. -/
def feistelLikeDesign : CryptoExpr :=
  .iterate 16 (.xor (.sbox 3 (.const 0)) (.linear 4 (.const 0)))

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Pipeline execution demonstrations
-- ══════════════════════════════════════════════════════════════════

/-- Run the full pipeline on a design. -/
def runPipeline (design : CryptoExpr) (weights : List Weights) : List (CryptoExpr × SecurityMetrics) :=
  let (rootId, g) := designToEGraph design EGraph.empty
  superhash_pipeline [] g 10 5 10 weights 10 rootId

-- AES-like design metrics
#eval
  let m := aesLikeDesign.metrics
  s!"AES-like: security={m.securityBits}, latency={m.latency}, gates={m.gateCount}"

-- Poseidon-like design metrics
#eval
  let m := poseidonLikeDesign.metrics
  s!"Poseidon-like: security={m.securityBits}, latency={m.latency}, gates={m.gateCount}"

-- Full pipeline execution (no rewrite rules, identity saturation)
#eval
  let result := runPipeline simpleSPN [⟨1, 1, 1⟩, ⟨2, 1, 1⟩, ⟨1, 2, 1⟩]
  s!"SPN pipeline: {result.length} Pareto-optimal designs"

-- Pipeline with multiple designs
#eval
  let result := runPipeline aesLikeDesign [⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 0, 1⟩]
  s!"AES pipeline: {result.length} Pareto-optimal designs"

-- E-graph stats after insertion
#eval
  let (_, g) := designToEGraph aesLikeDesign EGraph.empty
  let s := g.stats
  s!"AES E-graph: {s.numClasses} classes, {s.numNodes} nodes, UF size={s.unionFindSize}"

end SuperHash
