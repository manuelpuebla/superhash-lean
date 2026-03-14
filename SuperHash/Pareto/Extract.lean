import SuperHash.Pareto.Scalarization
import SuperHash.Pipeline.Soundness

/-!
# SuperHash.Pareto.Extract — Multi-objective Pareto extraction

Provides:
- `extractPareto`: for each weight vector, extract the best design from a saturated E-graph,
  then filter by Pareto front
- `computeMetrics`: compute SecurityMetrics from a CryptoExpr
- Design: scalarization (D5) → diverse extractions → Pareto filter

Limitation (D5): scalarization only finds convex hull of the Pareto front.
-/

namespace SuperHash

open UnionFind

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Metrics computation from extracted expressions
-- ══════════════════════════════════════════════════════════════════

/-- Compute SecurityMetrics from a CryptoExpr.
    Abstract cost model: security ∝ algebraic degree, latency ∝ depth, gates ∝ size. -/
def CryptoExpr.metrics : CryptoExpr → SecurityMetrics
  | .sbox d _ => ⟨d, 1, 1⟩
  | .linear b _ => ⟨b, 1, 1⟩
  | .xor l r =>
    let ml := l.metrics; let mr := r.metrics
    ⟨ml.securityBits + mr.securityBits, ml.latency + mr.latency, ml.gateCount + mr.gateCount + 1⟩
  | .round d b _ => ⟨d * b, 1, 2⟩
  | .compose f s =>
    let mf := f.metrics; let ms := s.metrics
    ⟨mf.securityBits + ms.securityBits, mf.latency + ms.latency, mf.gateCount + ms.gateCount⟩
  | .parallel l r =>
    let ml := l.metrics; let mr := r.metrics
    ⟨Nat.min ml.securityBits mr.securityBits,
     Nat.max ml.latency mr.latency,
     ml.gateCount + mr.gateCount⟩
  | .iterate n b =>
    let mb := b.metrics
    ⟨n * mb.securityBits, n * mb.latency, n * mb.gateCount⟩
  | .const _ => ⟨0, 0, 0⟩
  | .var _ => ⟨0, 0, 0⟩
  | .spnBlock r s l =>
    let ms := s.metrics; let ml := l.metrics
    ⟨r * (ms.securityBits + ml.securityBits),
     r * (ms.latency + ml.latency),
     r * (ms.gateCount + ml.gateCount)⟩
  | .feistelBlock r f =>
    let mf := f.metrics
    ⟨r * mf.securityBits, r * mf.latency, r * mf.gateCount⟩
  | .spongeBlock rt cap p =>
    let mp := p.metrics
    ⟨rt * mp.securityBits + cap, rt * mp.latency, rt * mp.gateCount⟩
  | .arxBlock r a rot x =>
    let ma := a.metrics; let mr := rot.metrics; let mx := x.metrics
    ⟨r * (ma.securityBits + mr.securityBits + mx.securityBits),
     r * (ma.latency + mr.latency + mx.latency),
     r * (ma.gateCount + mr.gateCount + mx.gateCount)⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Extract with single weight vector
-- ══════════════════════════════════════════════════════════════════

/-- Extract best design for a given weight vector.
    Compose: computeCostsF (with weighted cost) → extractAuto. -/
def extractWeighted (g : EGraph CryptoOp) (w : Weights) (costFuel : Nat)
    (rootId : EClassId) : Option CryptoExpr :=
  let g_cost := computeCostsF g (weightedCostFn w) costFuel
  extractAuto g_cost rootId

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Multi-objective Pareto extraction
-- ══════════════════════════════════════════════════════════════════

/-- Collect all extracted designs with their metrics. -/
def extractAll (g : EGraph CryptoOp) (weights : List Weights) (costFuel : Nat)
    (rootId : EClassId) : List (CryptoExpr × SecurityMetrics) :=
  (weights.filterMap (fun w => extractWeighted g w costFuel rootId)).map
    (fun e => (e, e.metrics))

/-- Remove duplicates by SecurityMetrics (keep first occurrence). -/
def dedup (designs : List (CryptoExpr × SecurityMetrics)) : List (CryptoExpr × SecurityMetrics) :=
  designs.foldl (fun acc p =>
    if acc.any (fun q => q.2 == p.2) then acc else acc ++ [p]) []

/-- Extract Pareto-optimal designs from a saturated E-graph.
    For each weight vector, extract the best design, compute metrics,
    then filter to the Pareto front.

    Algorithm:
    1. For each w ∈ weights: extractWeighted g w costFuel rootId
    2. Compute SecurityMetrics for each extracted design
    3. Remove duplicates
    4. Filter to Pareto front -/
def extractPareto (g : EGraph CryptoOp) (weights : List Weights) (costFuel : Nat)
    (rootId : EClassId) : List (CryptoExpr × SecurityMetrics) :=
  let all := extractAll g weights costFuel rootId
  let unique := dedup all
  let frontMetrics := paretoFront (unique.map (·.2))
  unique.filter (fun p => frontMetrics.any (fun m => decide (m = p.2)))

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Key property — extracted designs evaluate correctly
-- ══════════════════════════════════════════════════════════════════

/-- Each design extracted by extractWeighted evaluates to the root value.
    Direct corollary of computeCostsF_extractF_correct. -/
theorem extractWeighted_correct (g : EGraph CryptoOp) (w : Weights) (costFuel : Nat)
    (env : Nat → Nat) (v : EClassId → Nat)
    (hcv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (hsound : ExtractableSound CryptoOp CryptoExpr Nat)
    (rootId : EClassId) (expr : CryptoExpr)
    (hext : extractWeighted g w costFuel rootId = some expr) :
    EvalExpr.evalExpr expr env = v (root g.unionFind rootId) := by
  unfold extractWeighted at hext
  exact computeCostsF_extractF_correct g (weightedCostFn w) costFuel env v
    hcv hwf hbni hsound _ rootId expr hext

/-- All designs from extractAll evaluate to the root value. -/
theorem extractAll_correct (g : EGraph CryptoOp) (weights : List Weights) (costFuel : Nat)
    (env : Nat → Nat) (v : EClassId → Nat)
    (hcv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (hbni : BestNodeInv g.classes)
    (hsound : ExtractableSound CryptoOp CryptoExpr Nat)
    (rootId : EClassId) :
    ∀ p ∈ extractAll g weights costFuel rootId,
      EvalExpr.evalExpr p.1 env = v (root g.unionFind rootId) := by
  intro ⟨expr, m⟩ hmem
  simp only [extractAll, List.mem_map, List.mem_filterMap] at hmem
  obtain ⟨e, ⟨w, _hw, hew⟩, heq⟩ := hmem
  simp at heq
  obtain ⟨rfl, _⟩ := heq
  exact extractWeighted_correct g w costFuel env v hcv hwf hbni hsound rootId e hew

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Length bound — output size ≤ number of weight vectors
-- ══════════════════════════════════════════════════════════════════

/-- The number of designs from extractAll is at most the number of weight vectors. -/
theorem extractAll_length_le (g : EGraph CryptoOp) (weights : List Weights) (costFuel : Nat)
    (rootId : EClassId) :
    (extractAll g weights costFuel rootId).length ≤ weights.length := by
  simp only [extractAll, List.length_map]
  exact List.length_filterMap_le _ _

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Metrics bridge — p.2 = p.1.metrics for all output
-- ══════════════════════════════════════════════════════════════════

/-- Every element of extractAll has p.2 = p.1.metrics (by construction). -/
theorem extractAll_metrics_eq (g : EGraph CryptoOp) (weights : List Weights) (costFuel : Nat)
    (rootId : EClassId) :
    ∀ p ∈ extractAll g weights costFuel rootId, p.2 = p.1.metrics := by
  intro p hmem
  simp only [extractAll, List.mem_map] at hmem
  obtain ⟨e, _, rfl⟩ := hmem
  rfl

-- Smoke tests
#eval CryptoExpr.metrics (.round 7 5 (.const 0))       -- ⟨35, 1, 2⟩
#eval CryptoExpr.metrics (.compose (.sbox 7 (.const 0)) (.const 5))  -- ⟨7, 1, 1⟩
#eval CryptoExpr.metrics (.iterate 10 (.round 7 5 (.const 0)))       -- ⟨350, 10, 20⟩

end SuperHash
