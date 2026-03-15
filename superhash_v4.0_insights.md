# Insights: SuperHash v4.0 — Full Pipeline + LLM Ready

**Fecha**: 2026-03-15
**Base**: v3.3.1 (91 jobs, 0 sorry, ~1,100 thms)

## Key Findings

### 1. TrustHash Graph+DP Pipeline: ALL 17 files ZERO HashOp dependency
Every file in the constraint graph → tree decomposition → DP chain is standalone:
- Graph.lean (SimpleGraph, addEdge, neighbors) — drop-in
- EliminationOrder.lean (greedy min-degree for treewidth) — drop-in
- TreeDecomp.lean (tree decomposition structure) — drop-in
- NiceTreeConvert.lean (NiceNode 4-type inductive) — drop-in
- ConstraintGraph.lean (hash spec → SimpleGraph) — minimal adaptation
- TWBridge.lean (treewidth analysis bundle) — drop-in
- TreewidthDP.lean (exponential DP with DPTable) — 1 sorry, parametric
- DPCompose.lean (CostPair: security + performance) — drop-in
- DPOptimalSpec.lean (ValidNTD predicate) — drop-in
- DPOptimalProof.lean (dp_optimal_of_validNTD) — drop-in
- DPOperations.lean (cryptoDP catamorphism) — drop-in
- NiceTree.lean (niceTreeFold + invariant) — drop-in
- CryptoCost.lean (VertexCostParams + additiveCost) — drop-in
- Util/{NatOpt,FoldMin,InsertMin,DPBound} — 4 sorry total (utilities)

### 2. OptiSat ILP: ≤50 lines of new code
ALL types are domain-independent (ILPSolution, ILPConstraint, ILPProblem).
ALL functions are Op-parametric (encodeEGraph, checkSolution, extractILP).
ALL theorems are generic (extractILP_correct, ilp_extraction_soundness).
Integration = copy 5 files + instantiate for CryptoOp.

### 3. LLM Integration: Pipeline already exists, needs API connection
- RuleCandidate → RuleVerifier → RulePool infrastructure complete
- Python scripts exist: rule_proposer.py (templates), axle_integration.py (verification)
- Missing: actual LLM API calls (replace templates with Claude/Ollama)
- Missing: dynamic rule injection in designLoopStep (currently hard-coded)
- Missing: feedback loop (attribute Pareto improvements to rules)

## Implementation Strategy for v4.0

### Phase 1: TrustHash Graph Infrastructure (10 files, ~1,200 LOC)
Copy Graph.lean → EliminationOrder → TreeDecomp → NiceTreeConvert → ConstraintGraph → TWBridge.
All drop-in, no adaptation needed. Creates SuperHash/Graph/ directory.

### Phase 2: TrustHash Full DP Pipeline (7 files, ~1,100 LOC)
Copy TreewidthDP → DPCompose → DPOptimalSpec → DPOptimalProof → DPOperations + utilities.
Close the 5 sorry or document as concrete-only.

### Phase 3: ILP Extraction (5 files, ~1,200 LOC)
Copy from OptiSat: ILP.lean, ILPEncode.lean, ILPCheck.lean, ILPSpec.lean, Extraction.lean.
Add CryptoOp instantiation (~50 LOC new).

### Phase 4: LLM-Ready Python Integration
- Update rule_proposer.py with Ollama/Claude API client
- Update designLoopStep to use dynamic RulePool
- Create design_loop.py orchestrator
- Wire feedback: Pareto improvement → rule attribution → reward

### Phase 5: Expander Constructors (if time permits)
Add .expanderHash and .lpCompress to CryptoOp (13 files to update).

## Scoping Decision
Phases 1-4 are achievable in one session with quality.
Phase 5 and Boura-Canteaut/BitVec deferred to v4.1+.
The user explicitly wants "everything ready to connect the LLM tomorrow."
