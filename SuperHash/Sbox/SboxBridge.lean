-- SuperHash/Sbox/SboxBridge.lean
-- Bridge from concrete S-box analysis to pipeline parameters
-- SboxTable -> {DDT, LAT, AlgDegree} -> SboxAnalysis
-- Adapted from TrustHash/Sbox/SboxBridge.lean for Lean 4.28

import SuperHash.Sbox.SboxTable
import SuperHash.Sbox.DDTCompute
import SuperHash.Sbox.LATCompute
import SuperHash.Sbox.AlgDegreeCompute

namespace SuperHash.Sbox.SboxBridge

open SuperHash.Sbox
open SuperHash.Sbox.DDTCompute
open SuperHash.Sbox.LATCompute
open SuperHash.Sbox.AlgDegreeCompute

/-! ## SboxAnalysis: computed S-box security parameters

Bundles all three S-box analysis results (DDT, LAT, algebraic degree)
with verified upper bounds. -/

/-- Complete S-box analysis: all computed security parameters with bounds. -/
structure SboxAnalysis where
  inputBits      : Nat
  diffUniformity : Nat   -- delta from DDT (max_{a!=0,b} DDT[a][b])
  nonlinearity   : Nat   -- NL from LAT ((2^n - max|W|) / 2)
  algebraicDeg   : Nat   -- d from Moebius transform
  maxWalsh       : Nat   -- max_{a!=0,b!=0} |LAT[a][b]|
  h_delta_le     : diffUniformity ≤ 2 ^ inputBits
  h_deg_le       : algebraicDeg ≤ inputBits

/-! ## Computation -/

/-- Analyze a concrete S-box: compute DDT, LAT, algebraic degree.
    All results come with verified upper bounds. -/
def analyzeSbox (s : SboxTable) : SboxAnalysis where
  inputBits      := s.inputBits
  diffUniformity := diffUniformityFromTable s
  nonlinearity   := nonlinearityFromTable s
  algebraicDeg   := algebraicDegreeFromTable s
  maxWalsh       := maxWalshBias s
  h_delta_le     := diffUniformity_le s
  h_deg_le       := algebraicDegreeFromTable_le s

/-! ## Bridge theorems

These connect computed values to the well-formedness
constraints required by downstream pipeline types. -/

/-- The computed diffUniformity is bounded by 2^n. -/
theorem analyzeSbox_delta_le (s : SboxTable) :
    (analyzeSbox s).diffUniformity ≤ 2 ^ s.inputBits := by
  exact (analyzeSbox s).h_delta_le

/-- The computed algebraic degree is bounded by n. -/
theorem analyzeSbox_deg_le (s : SboxTable) :
    (analyzeSbox s).algebraicDeg ≤ s.inputBits := by
  exact (analyzeSbox s).h_deg_le

/-- The computed maxWalsh is bounded by 2^n. -/
theorem analyzeSbox_walsh_le (s : SboxTable) :
    (analyzeSbox s).maxWalsh ≤ 2 ^ s.inputBits := by
  unfold analyzeSbox; exact maxWalshBias_le s

/-- The computed inputBits matches the source S-box. -/
theorem analyzeSbox_bits (s : SboxTable) :
    (analyzeSbox s).inputBits = s.inputBits := rfl

/-! ## Concrete instances -/

/-- PRESENT 4-bit S-box analysis. -/
def presentAnalysis : SboxAnalysis := analyzeSbox presentSbox

/-- PRESENT: delta = 4 (verified from lookup table). -/
theorem presentAnalysis_delta : presentAnalysis.diffUniformity = 4 := by native_decide

/-- PRESENT: NL = 4 (verified from lookup table). -/
theorem presentAnalysis_nl : presentAnalysis.nonlinearity = 4 := by native_decide

/-- PRESENT: algebraic degree = 3 (verified from lookup table). -/
theorem presentAnalysis_deg : presentAnalysis.algebraicDeg = 3 := by native_decide

/-- PRESENT: max Walsh bias = 8 (verified from lookup table). -/
theorem presentAnalysis_walsh : presentAnalysis.maxWalsh = 8 := by native_decide

/-- PRESENT: delta >= 2. -/
theorem presentAnalysis_delta_ge : presentAnalysis.diffUniformity ≥ 2 := by native_decide

/-- PRESENT: delta >= 1. -/
theorem presentAnalysis_delta_pos : presentAnalysis.diffUniformity ≥ 1 := by native_decide

/-- PRESENT: degree >= 2. -/
theorem presentAnalysis_deg_ge : presentAnalysis.algebraicDeg ≥ 2 := by native_decide

/-- Toy 2-bit S-box analysis. -/
def toy2Analysis : SboxAnalysis := analyzeSbox toy2Sbox

theorem toy2Analysis_delta : toy2Analysis.diffUniformity = 4 := by native_decide
theorem toy2Analysis_nl : toy2Analysis.nonlinearity = 0 := by native_decide
theorem toy2Analysis_deg : toy2Analysis.algebraicDeg = 1 := by native_decide

/-- Toy 3-bit S-box analysis. -/
def toy3Analysis : SboxAnalysis := analyzeSbox toy3Sbox

theorem toy3Analysis_delta : toy3Analysis.diffUniformity = 8 := by native_decide
theorem toy3Analysis_nl : toy3Analysis.nonlinearity = 0 := by native_decide
theorem toy3Analysis_deg : toy3Analysis.algebraicDeg = 2 := by native_decide

end SuperHash.Sbox.SboxBridge
