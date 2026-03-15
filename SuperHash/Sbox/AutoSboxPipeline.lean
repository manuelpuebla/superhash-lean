-- SuperHash/Sbox/AutoSboxPipeline.lean
-- Automated S-box certification pipeline:
-- SboxTable -> compute DDT/LAT/AlgDeg -> SboxFullCert -> SboxAnalysis
-- THE CROWN JEWEL: autoSboxPipeline : SboxTable -> SboxAnalysis
-- Adapted from TrustHash/Sbox/AutoSboxPipeline.lean for Lean 4.28

import SuperHash.Sbox.SboxFullCert

namespace SuperHash.Sbox.AutoSboxPipeline

open SuperHash.Sbox
open SuperHash.Sbox.DDTCompute
open SuperHash.Sbox.DDTCertificate
open SuperHash.Sbox.LATCompute
open SuperHash.Sbox.LATCertificate
open SuperHash.Sbox.AlgDegreeCompute
open SuperHash.Sbox.SboxFullCert
open SuperHash.Sbox.SboxBridge

/-! ## Automated Certificate Generation

Pipeline: SboxTable -> compute DDT/LAT/degree -> SboxFullCert -> SboxAnalysis.

The key insight: we generate certificates by computation, then verify them.
This separates the trusted kernel (checker) from the untrusted computation. -/

/-- Generate a full certificate from a concrete S-box.
    Computes all three properties and packages them. -/
def generateFullCert (sbox : SboxTable) : SboxFullCert where
  ddtCert := { inputBits := sbox.inputBits
               maxDelta := diffUniformityFromTable sbox }
  latCert := { inputBits := sbox.inputBits
               maxBias := maxWalshBias sbox
               nonlinearity := nonlinearityFromTable sbox }
  algDegreeCert := { inputBits := sbox.inputBits
                     degree := algebraicDegreeFromTable sbox }

/-- Generated certificates always pass the DDT checker. -/
theorem generateFullCert_ddt_valid (sbox : SboxTable) :
    checkDDT (generateFullCert sbox).ddtCert sbox = true := by
  unfold generateFullCert checkDDT
  simp [BEq.beq]

/-- Generated certificates always pass the LAT checker. -/
theorem generateFullCert_lat_valid (sbox : SboxTable) :
    checkLAT (generateFullCert sbox).latCert sbox = true := by
  unfold generateFullCert checkLAT
  simp [BEq.beq]

/-- Generated certificates always pass the AlgDegree checker. -/
theorem generateFullCert_algdeg_valid (sbox : SboxTable) :
    checkAlgDegree (generateFullCert sbox).algDegreeCert sbox = true := by
  unfold generateFullCert checkAlgDegree
  simp [BEq.beq]

/-- Generated certificates always pass the full checker. -/
theorem generateFullCert_valid (sbox : SboxTable) :
    checkSboxFull (generateFullCert sbox) sbox = true := by
  unfold checkSboxFull
  rw [generateFullCert_ddt_valid, generateFullCert_lat_valid,
      generateFullCert_algdeg_valid]
  rfl

/-! ## End-to-End Pipeline

The full automated pipeline: SboxTable -> certified SboxAnalysis. -/

/-- Full pipeline: generate certificate, verify it, extract analysis.
    Takes raw S-box table, computes DDT + LAT + algebraic degree,
    returns certified SboxAnalysis with all bounds verified. -/
def autoSboxPipeline (sbox : SboxTable) : SboxAnalysis :=
  let cert := generateFullCert sbox
  let hv := generateFullCert_valid sbox
  sboxAnalysisFromCert cert sbox hv

/-- Pipeline output matches direct analyzeSbox on delta. -/
theorem autoSboxPipeline_delta_eq (sbox : SboxTable) :
    (autoSboxPipeline sbox).diffUniformity = (analyzeSbox sbox).diffUniformity := by
  unfold autoSboxPipeline
  exact (sboxAnalysisFromCert_eq _ sbox (generateFullCert_valid sbox)).1

/-- Pipeline output matches direct analyzeSbox on nonlinearity. -/
theorem autoSboxPipeline_nl_eq (sbox : SboxTable) :
    (autoSboxPipeline sbox).nonlinearity = (analyzeSbox sbox).nonlinearity := by
  unfold autoSboxPipeline
  exact (sboxAnalysisFromCert_eq _ sbox (generateFullCert_valid sbox)).2.1

/-- Pipeline output matches direct analyzeSbox on algebraic degree. -/
theorem autoSboxPipeline_deg_eq (sbox : SboxTable) :
    (autoSboxPipeline sbox).algebraicDeg = (analyzeSbox sbox).algebraicDeg := by
  unfold autoSboxPipeline
  exact (sboxAnalysisFromCert_eq _ sbox (generateFullCert_valid sbox)).2.2

/-- Pipeline preserves inputBits. -/
theorem autoSboxPipeline_bits (sbox : SboxTable) :
    (autoSboxPipeline sbox).inputBits = sbox.inputBits := rfl

/-! ## Helper extractors -/

/-- Extract delta from pipeline output. -/
def pipelineDelta (sbox : SboxTable) : Nat :=
  (autoSboxPipeline sbox).diffUniformity

/-- Extract degree from pipeline output. -/
def pipelineDegree (sbox : SboxTable) : Nat :=
  (autoSboxPipeline sbox).algebraicDeg

/-- Extract nonlinearity from pipeline output. -/
def pipelineNL (sbox : SboxTable) : Nat :=
  (autoSboxPipeline sbox).nonlinearity

/-! ## Concrete Validation -/

/-- PRESENT auto-generated params: delta = 4. -/
theorem present_auto_delta : pipelineDelta presentSbox = 4 := by native_decide

/-- PRESENT auto-generated params: degree = 3. -/
theorem present_auto_degree : pipelineDegree presentSbox = 3 := by native_decide

/-- PRESENT auto-generated params: nonlinearity = 4. -/
theorem present_auto_nl : pipelineNL presentSbox = 4 := by native_decide

/-- Toy 2-bit pipeline results. -/
theorem toy2_auto_delta : pipelineDelta toy2Sbox = 4 := by native_decide
theorem toy2_auto_degree : pipelineDegree toy2Sbox = 1 := by native_decide
theorem toy2_auto_nl : pipelineNL toy2Sbox = 0 := by native_decide

/-- Toy 3-bit pipeline results. -/
theorem toy3_auto_delta : pipelineDelta toy3Sbox = 8 := by native_decide
theorem toy3_auto_degree : pipelineDegree toy3Sbox = 2 := by native_decide
theorem toy3_auto_nl : pipelineNL toy3Sbox = 0 := by native_decide

/-! ## Pipeline-to-SboxAnalysis consistency -/

/-- Pipeline output is consistent with SboxAnalysis for PRESENT delta. -/
theorem present_pipeline_consistent_delta :
    pipelineDelta presentSbox = (analyzeSbox presentSbox).diffUniformity := by
  native_decide

/-- Pipeline output is consistent with SboxAnalysis for PRESENT nonlinearity. -/
theorem present_pipeline_consistent_nl :
    pipelineNL presentSbox = (analyzeSbox presentSbox).nonlinearity := by
  native_decide

/-! ## Non-vacuity: autoSboxPipeline evaluates to concrete values

These #eval tests demonstrate the pipeline produces real results
at compile time, not just satisfies types vacuously. -/

#eval do
  let analysis := autoSboxPipeline presentSbox
  IO.println s!"PRESENT: delta={analysis.diffUniformity}, NL={analysis.nonlinearity}, deg={analysis.algebraicDeg}, maxWalsh={analysis.maxWalsh}"

#eval do
  let analysis := autoSboxPipeline toy2Sbox
  IO.println s!"Toy2: delta={analysis.diffUniformity}, NL={analysis.nonlinearity}, deg={analysis.algebraicDeg}"

#eval do
  let analysis := autoSboxPipeline toy3Sbox
  IO.println s!"Toy3: delta={analysis.diffUniformity}, NL={analysis.nonlinearity}, deg={analysis.algebraicDeg}"

end SuperHash.Sbox.AutoSboxPipeline
