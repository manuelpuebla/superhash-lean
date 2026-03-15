-- SuperHash v2.0: Verified autonomous hash design via E-graphs + LLM discovery
import SuperHash.CryptoOp
import SuperHash.DesignParams
import SuperHash.Pareto
import SuperHash.Instances
import SuperHash.CryptoNodeOps
import SuperHash.EGraph.UnionFind
import SuperHash.EGraph.Core
import SuperHash.EGraph.CoreSpec
import SuperHash.EGraph.EMatch
import SuperHash.EGraph.Consistency
import SuperHash.EGraph.AddNodeTriple
import SuperHash.EGraph.Tests
import SuperHash.Rules.SoundRule
import SuperHash.Rules.CryptoRules
import SuperHash.Rules.NonVacuity
import SuperHash.Rules.BlockBridge
import SuperHash.Pipeline.Saturate
import SuperHash.Pipeline.EMatchSpec
import SuperHash.Pipeline.Extract
import SuperHash.Pipeline.Instances
import SuperHash.Pipeline.Soundness
import SuperHash.Pareto.Scalarization
import SuperHash.Pareto.Extract
import SuperHash.Pareto.Soundness
import SuperHash.Pipeline.Integration
import SuperHash.Pipeline.MasterTheorem
import SuperHash.Instances.Evaluation
import SuperHash.Instances.BlockDesigns
import SuperHash.Discovery.RuleCandidate
import SuperHash.Discovery.RuleVerifier
import SuperHash.Discovery.RulePool
import SuperHash.Concrete.BitVecOps
import SuperHash.Concrete.Bridge
import SuperHash.SmoothE.CostModel
import SuperHash.SmoothE.Extract
import SuperHash.DesignLoop.Core
import SuperHash.DesignLoop.Soundness
import SuperHash.Pipeline.MasterTheoremV2
-- v2.5: Real crypto semantics
import SuperHash.Crypto.Semantics
import SuperHash.Crypto.CryptoEval
import SuperHash.Crypto.CryptoRule
import SuperHash.Crypto.DDT
import SuperHash.Crypto.AlgebraicDegree
import SuperHash.Crypto.Fitness
import SuperHash.Crypto.SourceEntropy
import SuperHash.Crypto.ExtractorBound
import SuperHash.Crypto.UHFConstraint
import SuperHash.Crypto.ZKSideInfo
import SuperHash.Crypto.AESSbox
import SuperHash.Crypto.CryptoNodeSemantics
import SuperHash.Crypto.BouraCanteutBound
import SuperHash.Crypto.SecurityNotions
import SuperHash.Crypto.HigherOrderDiff
import SuperHash.Crypto.LinearLayerDegree
import SuperHash.Pipeline.CompletenessSpec
import SuperHash.Bridge.TrustHashFitness
import SuperHash.TrustHash.NiceTree
import SuperHash.TrustHash.Verdict
import SuperHash.Rules.CryptoRulesCS
import SuperHash.Pipeline.MasterTheoremCS
import SuperHash.Rules.ExpansionRules
import SuperHash.Crypto.ExpanderBounds
-- v3.3 Phase 1: S-box computation foundation
import SuperHash.Sbox.Bitwise
import SuperHash.Sbox.FinIter
import SuperHash.Sbox.SboxTable
import SuperHash.Sbox.DDTCompute
import SuperHash.Sbox.LATCompute
import SuperHash.Sbox.AlgDegreeCompute
import SuperHash.Sbox.DDTCertificate
import SuperHash.Sbox.LATCertificate
import SuperHash.Sbox.SboxBridge
import SuperHash.Sbox.SboxFullCert
import SuperHash.Sbox.AutoSboxPipeline
import SuperHash.Sbox.AES8BitCertified
-- v3.3 Phase 2: Security modules
import SuperHash.Security.ThreatLattice4D
import SuperHash.Security.ActiveSboxBounds
import SuperHash.Security.QuantumBounds
import SuperHash.Security.DivisionProperty.Spec
import SuperHash.Security.DivisionProperty.Propagation
import SuperHash.Security.DivisionProperty.CostModel
import SuperHash.Security.AlgExpr
import SuperHash.Security.ConditionalRewriteRule
import SuperHash.Security.SecurityVerdict
-- v3.3 Phase 3: Extended 6D Pareto optimization
import SuperHash.Pareto.ExtendedMetrics
import SuperHash.Pareto.ExtendedDominance
import SuperHash.Pareto.ExtendedExtract
import SuperHash.Pareto.PipelineBridge
import SuperHash.Sbox.SboxParetoBridge
-- v4.0 Phase 3: ILP extraction infrastructure
import SuperHash.Pipeline.ILP
import SuperHash.Pipeline.ILPEncode
import SuperHash.Pipeline.ILPCheck
import SuperHash.Pipeline.ILPSpec
import SuperHash.Pipeline.ExtractionStrategy
import SuperHash.Pipeline.ILPInstances
-- v4.0 Phase 1: Graph infrastructure (from TrustHash)
import SuperHash.Graph.SimpleGraph
import SuperHash.Graph.EliminationOrder
import SuperHash.Graph.TreeDecomp
import SuperHash.Graph.NiceTreeConvert
import SuperHash.Graph.ConstraintGraph
import SuperHash.Graph.TWBridge
-- v4.0 Phase 2: DP pipeline (from TrustHash)
import SuperHash.Graph.Util.NatOpt
import SuperHash.Graph.Util.FoldMin
import SuperHash.Graph.Util.InsertMin
import SuperHash.Graph.TreewidthDP
import SuperHash.Graph.DPCompose
import SuperHash.Graph.DPOptimal
import SuperHash.Graph.CryptoCost
-- v4.5 Phase 1: Attack Foundation (Red Team)
import SuperHash.Attack.AttackOp
import SuperHash.Attack.AttackSemantics
import SuperHash.Attack.AttackNodeSemantics
-- v4.5 Phase 2: Attack Pipeline
import SuperHash.Attack.AttackExpr
import SuperHash.Attack.AttackInstances
import SuperHash.Attack.AttackPipeline
-- v4.5 Phase 3: Attack Rules + Metrics
import SuperHash.Attack.AttackMetrics
import SuperHash.Attack.AttackRules
-- v4.5 Phase 4: Bridge + Duel
import SuperHash.Attack.HashSpecBridge
import SuperHash.Attack.DuelTheorem
-- v4.5 Phase 5: Co-Evolution Loop + Non-Vacuity
import SuperHash.Attack.DuelLoop
import SuperHash.Attack.NonVacuity
