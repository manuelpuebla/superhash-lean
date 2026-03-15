# Insights: SuperHash v3.3 — Full Pipeline + Design Space Expansion

**Fecha**: 2026-03-15
**Base**: v3.2.0 (65 jobs, 0 sorry, ~800 thms, pipeline_soundness_crypto)

## 1. TrustHash Deep Inventory

**189 source files, 35,487 LOC, 3,463 declarations, Lean 4.16.0**

### Classification
| Category | EASY_COPY | NEEDS_ADAPTATION | ALREADY_ADAPTED | SKIP |
|----------|-----------|------------------|-----------------|------|
| S-box Pipeline (16) | 15 | 1 | 0 | 0 |
| E-graph Engine (20) | 0 | 6 | 0 | 14 |
| DP / Tree Decomp (16) | 7 | 5 | 4 | 0 |
| Graph Infrastructure (8) | 7 | 1 | 0 | 0 |
| Hash Domain Types (8) | 3 | 5 | 0 | 0 |
| Security Model (12) | 6 | 1 | 3 | 1 |
| Rewrite Rules (7) | 5 | 2 | 0 | 0 |
| Attacks Framework (13) | 10 | 3 | 0 | 0 |
| Cipher Models (15) | 13 | 2 | 0 | 0 |
| Degree / Trail (10) | 10 | 0 | 0 | 0 |
| Math Foundations (8) | 8 | 0 | 0 | 0 |
| Pipeline / Integration (10) | 2 | 5 | 3 | 0 |
| **Total** | **97** | **36** | **10** | **44** |

### Top 10 Highest-Value Files
1. `Sbox/AutoSboxPipeline.lean` (195 LOC, EASY) — S-box → DDT/LAT/deg → CertifiedParams
2. `Sbox/DDTCertificate.lean` (265 LOC, EASY) — Offline DDT certificate for 8-bit S-boxes
3. `HashSoundRules.lean` (481 LOC, ADAPT) — 12+ sound rewrite rules for hash expressions
4. `DP/TreewidthDP.lean` (407 LOC, ADAPT) — Full O(k^tw) DP on tree decompositions
5. `Attacks/QuantumBounds.lean` (188 LOC, EASY) — Grover + BHT quantum bounds
6. `ThreatLattice4D.lean` (361 LOC, EASY) — 4D threat model lattice (COL×LE×OC×IL)
7. `ConditionalRewriteRule.lean` (184 LOC, EASY) — Conditional rewrites with side conditions
8. `Attacks/DivisionProperty/*.lean` (572 LOC, EASY) — Division property integral cryptanalysis
9. `EGraph/RecursiveRewrite.lean` (172 LOC, ADAPT) — Depth-aware recursive rewriting
10. `DP/DPCompose.lean` (205 LOC, ADAPT) — Multi-criteria DP (security + performance)

### Key Architectural Barrier
Type divergence: TrustHash uses `HashOp` (SPN+Keccak constructors, `ClassRef` children) vs SuperHash's `CryptoOp` (algebraic constructors, `EClassId` children). The 36 NEEDS_ADAPTATION files all depend on `HashOp`. Two strategies:
- **(A) Bridge**: Create `HashOp ↔ CryptoOp` translation functions (modular but duplicates)
- **(B) Unify**: Merge both into a single expanded type (invasive but clean)

**Recommendation**: Strategy (A) with bridge functions. Keeps SuperHash autonomous.

## 2. Library Reuse Map

### DynamicTreeProg (122 theorems) — CRITICAL for TrustHash DP
| Theorem | Use in SuperHash v3.3 |
|---------|----------------------|
| `treeFold_inv` | Master induction lemma for `runDP` correctness |
| `forget/join/introduce_preserves_bound` | Per-node DP correctness (3 theorems) |
| `opt_substructure` | Bellman optimality principle |
| `foldl_min_attained` | Existence of optimal solution in DP tables |
| `treeFold_combined_lower_bound` | Combined diff+alg analysis |
| `treeFold_mono` | Monotonicity for `differential_mono_rounds` |
| `additiveCost_append` | Path cost decomposition in nice trees |
| `insertMin_le_new/old` | DP table update correctness |

### VerifiedExtraction (129 theorems) — ILP + DP extraction
| Theorem | Use |
|---------|-----|
| `dp_optimal_of_validNTD` | DP extraction is optimal given valid NTD |
| `extractILP_correct` | ILP certificate extraction correctness |
| `ValidNTD` predicate | Validity of nice tree decompositions |
| `runDP_DPCompleteInv` | Master DP correctness |
| `ExtractionStrategy` inductive | Three strategies: greedy/ILP/treewidthDP |
| `extract_correct` | Unified extraction correctness |

### OptiSat (190+ theorems) — ILP pipeline
| Theorem | Use |
|---------|-----|
| `full_pipeline_soundness` | End-to-end pipeline (parametric over Val) |
| `extractILP_correct` | ILP extraction with certificate |
| `extractAuto_complete` | Extraction completeness (always succeeds) |
| `ilp_extraction_soundness` | ILP composed soundness |
| `optimizeWithStrategyF_soundness` | Multi-strategy pipeline |

### LeanHash (440 theorems) — Security + Pareto
| Theorem | Use |
|---------|-----|
| `DesignSpace.dominates` + partial order | Pareto dominance definition |
| `ThreatLattice.ThreatModel` | 4D threat model lattice |
| `security_monotone` | Conservative verdicts |
| `MerkleDamgard.compress_collision_implies_hash_collision` | MD soundness |
| `JouxMulticollision.path_treewidth` | Links treewidth to construction type |
| `SPNDegree.full_round_degree` | SPN degree analysis |

### ProofKit (20 theorems) — Pipeline composition
- `foldl_inv_extends` — saturation loop proofs
- `HashMap.foldl_preserves` — EGraph iteration
- `foldl_pair_inv_extends` — tracking two properties simultaneously

## 3. Gap Analysis (6 tasks)

### Task 1: TrustHash Full Pipeline (97 EASY_COPY files)
**Strategy**: Copy in 4 tiers by dependency:
- **Tier 0** (leaves, ~20 files): Math foundations, Bitwise, FinIter, AlgExpr, RoundStructure
- **Tier 1** (S-box, ~16 files): SboxTable → DDTCompute → LATCompute → AutoSboxPipeline → Certificates
- **Tier 2** (Graph+DP, ~15 files): Graph → EliminationOrder → TreeDecomp → NiceTreeConvert → DPOptimal
- **Tier 3** (Security+Attacks, ~25 files): SecurityDefs, ThreatLattice4D, ActiveSboxBounds, QuantumBounds, DivisionProperty, Cipher models
- **Tier 4** (Integration, ~10 files): Pipeline wiring, End-to-end, ConditionalRewriteRules

**Effort**: ~14,200 LOC to copy (Tiers 0-3), ~8,000 LOC to adapt (Tier 4 + HashOp bridges)
**Expected bugs**: ~20 (at L-523 rate of 1/700 LOC)
**Difficulty**: MEDIUM (mechanical, high volume)

### Task 2: SecurityProfile in Pareto (4-dim optimization)
**What changes**: Extend `SecurityMetrics` (3 fields) to include RS 4-dim profile, or create parallel `SecurityProfileMetrics`. Update dominance, scalarization, extraction.
- New `Pareto/SecurityProfileMetrics.lean`
- Modify 8 files (Pareto/*, Pipeline/Integration, MasterTheorem*)
- ~15-20 new theorems
**Difficulty**: MEDIUM-HIGH (wide ripple effect)

### Task 3: Expander Constructors (.expanderHash, .lpCompress)
**What changes**: Add 2 constructors to CryptoOp → update 13 files with new match arms. Each file needs 2 new arms in every pattern match.
- `evalCryptoOpCS` gets 2 new semantic clauses
- `crypto_extractable_sound_cs` grows from 12 to 14 cases
- Expansion rules for expander ↔ iterate/compose bridges
**Difficulty**: MEDIUM (mechanical, touches many files)

### Task 4: ILP Extraction (from OptiSat/VerifiedExtraction)
**What to copy**: `ILPSolution`, `ValidSolution`, `extractILP`, `extractILP_correct`, `checkSolution`
**Integration**: Add ILP as alternative to greedy in `extractPareto`. Certificate-based: solver runs externally, Lean verifies the certificate.
**Difficulty**: MEDIUM (well-understood from OptiSat)

### Task 5: Boura-Canteaut General Proof (Reed-Muller)
**Required**: BoolFn definition, RM(r,m) code, covering radius theorem, Walsh divisibility
**Estimated**: ~800-1100 LOC, ~30-40 theorems, 3 new files
**Difficulty**: VERY HIGH — no proof assistant has this formalized
**Feasible path**: Start with the special case deg(F⁻¹) = n-1 (covers AES, PRESENT). This avoids the full RM covering radius and only needs permutation properties over GF(2)^n.

### Task 6: BitVec End-to-End
**Current state**: Only `.xor` and `.const` have concrete BitVec semantics. Everything else falls back to abstract Nat.
**Needed**: Concrete `evalCryptoOpBitVec` for all 12+ constructors, pipeline bridge theorem
**Difficulty**: HIGH (XOR divergence: abstract=addition, concrete=bitwise → partial bridge only)

## 4. Recommended Implementation Order

```
Phase 1: TrustHash S-box Pipeline (Tier 1: 16 files, EASY_COPY)
  ↓ unlocks: real S-box certification, DDT/LAT certificates, AutoSboxPipeline
Phase 2: TrustHash Graph + DP (Tier 2: 15 files, EASY_COPY + adapt)
  ↓ unlocks: constraint graphs, tree decomposition, full DP with optimality
Phase 3: TrustHash Security + Attacks (Tier 3: 25 files, EASY_COPY)
  ↓ unlocks: quantum bounds, division property, slide attacks, threat lattice
Phase 4: SecurityProfile in Pareto (new + modify 8 files)
  ↓ unlocks: multi-property Pareto optimization
Phase 5: ILP Extraction (copy from OptiSat, 5 files)
  ↓ unlocks: optimal extraction with certificate verification
Phase 6: Expander Constructors (modify 13 files)
  ↓ unlocks: expanded design space with provable expander security
Phase 7: Boura-Canteaut General (3 new files, VERY HIGH)
  ↓ unlocks: first formalized BC bound in any proof assistant
Phase 8: BitVec End-to-End (2 new + 3 modify)
  ↓ unlocks: concrete verification of extracted designs
```

## 5. Risk Assessment

| Phase | Risk | Mitigation |
|-------|------|-----------|
| 1 (S-box) | LOW — self-contained, no HashOp deps | Build after each file |
| 2 (Graph+DP) | MEDIUM — DP needs adaptation to NiceNode vs NiceTree | Use DynamicTreeProg theorems as templates |
| 3 (Attacks) | LOW — mostly self-contained | Skip HashOp-dependent instances |
| 4 (Pareto) | HIGH — wide ripple through pipeline | Additive approach: extend, don't replace |
| 5 (ILP) | MEDIUM — well-understood from OptiSat | Certificate approach (external solver) |
| 6 (Expander) | MEDIUM — 13 files to update | Add arms incrementally, build often |
| 7 (BC General) | VERY HIGH — novel formalization | Start with special case (bijective S-box) |
| 8 (BitVec) | HIGH — XOR divergence is fundamental | Partial bridge (bounded domain only) |

## 6. Estimated Impact

| Metric | v3.2 | v3.3 (target) |
|--------|------|--------------|
| Build jobs | 65 | ~120 |
| LOC | ~19K | ~35K |
| Theorems | ~800 | ~1,400 |
| Sorry | 0 | 0 |
| TrustHash coverage | 2/189 files | ~100/189 files |
| Attack types modeled | 3 (birthday, diff, alg) | 8+ (+ quantum, division, slide, related-key, invariant) |
| Extraction strategies | 1 (greedy) | 3 (greedy + ILP + treewidth DP) |
| Security dimensions | 1 (scalar) | 4 (Rogaway-Shrimpton) |
