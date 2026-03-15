-- SuperHash/Sbox/SboxFullCert.lean
-- Unified S-box certification: DDT + LAT + AlgDegree -> SboxFullCert
-- Combines three independent certificates into one verified bundle
-- Adapted from TrustHash/Sbox/SboxFullCert.lean for Lean 4.28

import SuperHash.Sbox.DDTCertificate
import SuperHash.Sbox.LATCertificate
import SuperHash.Sbox.AlgDegreeCompute
import SuperHash.Sbox.SboxBridge

namespace SuperHash.Sbox.SboxFullCert

open SuperHash.Sbox
open SuperHash.Sbox.DDTCompute
open SuperHash.Sbox.DDTCertificate
open SuperHash.Sbox.LATCompute
open SuperHash.Sbox.LATCertificate
open SuperHash.Sbox.AlgDegreeCompute
open SuperHash.Sbox.SboxBridge

/-! ## Algebraic Degree Certificate

An AlgDegree certificate follows the same pattern as DDT/LAT. -/

/-- Certificate for algebraic degree of an S-box. -/
structure AlgDegreeCert where
  /-- Bit width of the S-box -/
  inputBits : Nat
  /-- Claimed algebraic degree -/
  degree : Nat
  deriving Repr, DecidableEq

/-- Check an algebraic degree certificate against an S-box. -/
def checkAlgDegree (cert : AlgDegreeCert) (sbox : SboxTable) : Bool :=
  cert.inputBits == sbox.inputBits &&
  cert.degree == algebraicDegreeFromTable sbox

/-- Soundness: if checker passes, degree matches computation. -/
theorem checkAlgDegree_sound (cert : AlgDegreeCert) (sbox : SboxTable)
    (h : checkAlgDegree cert sbox = true) :
    cert.degree = algebraicDegreeFromTable sbox := by
  unfold checkAlgDegree at h
  have := Bool.and_eq_true_iff.mp h
  exact eq_of_beq this.2

/-- Bit width soundness for algebraic degree certificate. -/
theorem checkAlgDegree_bits (cert : AlgDegreeCert) (sbox : SboxTable)
    (h : checkAlgDegree cert sbox = true) :
    cert.inputBits = sbox.inputBits := by
  unfold checkAlgDegree at h
  have := Bool.and_eq_true_iff.mp h
  exact eq_of_beq this.1

/-- Upper bound: certified degree bounded by input bits. -/
theorem checkAlgDegree_upper_bound (cert : AlgDegreeCert) (sbox : SboxTable)
    (h : checkAlgDegree cert sbox = true) :
    cert.degree ≤ sbox.inputBits := by
  rw [checkAlgDegree_sound cert sbox h]
  exact algebraicDegreeFromTable_le sbox

/-- PRESENT algebraic degree certificate: degree = 3. -/
def presentAlgDegreeCert : AlgDegreeCert :=
  { inputBits := 4, degree := 3 }

theorem present_algdeg_valid : checkAlgDegree presentAlgDegreeCert presentSbox = true := by
  native_decide

/-- Toy 2-bit algebraic degree certificate: degree = 1. -/
def toy2AlgDegreeCert : AlgDegreeCert :=
  { inputBits := 2, degree := 1 }

theorem toy2_algdeg_valid : checkAlgDegree toy2AlgDegreeCert toy2Sbox = true := by
  native_decide

/-- Toy 3-bit algebraic degree certificate: degree = 2. -/
def toy3AlgDegreeCert : AlgDegreeCert :=
  { inputBits := 3, degree := 2 }

theorem toy3_algdeg_valid : checkAlgDegree toy3AlgDegreeCert toy3Sbox = true := by
  native_decide

/-! ## Full S-box Certificate

Combines DDT certificate, LAT certificate, and algebraic degree certificate
into one verified bundle. All three must pass for the full cert to be valid. -/

/-- Full S-box certification: all three properties verified. -/
structure SboxFullCert where
  /-- DDT certificate (differential uniformity) -/
  ddtCert : DDTCertificate
  /-- LAT certificate (max Walsh bias + nonlinearity) -/
  latCert : LATCertificate
  /-- Algebraic degree certificate -/
  algDegreeCert : AlgDegreeCert
  deriving Repr

/-- Check all three certificates against an S-box. -/
def checkSboxFull (cert : SboxFullCert) (sbox : SboxTable) : Bool :=
  checkDDT cert.ddtCert sbox &&
  checkLAT cert.latCert sbox &&
  checkAlgDegree cert.algDegreeCert sbox

private theorem full_and3_1 {a b c : Bool} (h : (a && b && c) = true) : a = true := by
  cases a <;> simp_all

private theorem full_and3_2 {a b c : Bool} (h : (a && b && c) = true) : b = true := by
  cases a <;> cases b <;> simp_all

private theorem full_and3_3 {a b c : Bool} (h : (a && b && c) = true) : c = true := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- Full certificate soundness: DDT part is sound. -/
theorem checkSboxFull_ddt_sound (cert : SboxFullCert) (sbox : SboxTable)
    (h : checkSboxFull cert sbox = true) :
    cert.ddtCert.maxDelta = diffUniformityFromTable sbox := by
  unfold checkSboxFull at h
  exact checkDDT_sound cert.ddtCert sbox (full_and3_1 h)

/-- Full certificate soundness: LAT part is sound. -/
theorem checkSboxFull_lat_sound (cert : SboxFullCert) (sbox : SboxTable)
    (h : checkSboxFull cert sbox = true) :
    cert.latCert.maxBias = maxWalshBias sbox := by
  unfold checkSboxFull at h
  exact checkLAT_sound cert.latCert sbox (full_and3_2 h)

/-- Full certificate soundness: algebraic degree part is sound. -/
theorem checkSboxFull_algdeg_sound (cert : SboxFullCert) (sbox : SboxTable)
    (h : checkSboxFull cert sbox = true) :
    cert.algDegreeCert.degree = algebraicDegreeFromTable sbox := by
  unfold checkSboxFull at h
  exact checkAlgDegree_sound cert.algDegreeCert sbox (full_and3_3 h)

/-- Full certificate soundness: nonlinearity part is sound. -/
theorem checkSboxFull_nl_sound (cert : SboxFullCert) (sbox : SboxTable)
    (h : checkSboxFull cert sbox = true) :
    cert.latCert.nonlinearity = nonlinearityFromTable sbox := by
  unfold checkSboxFull at h
  exact checkLAT_nl cert.latCert sbox (full_and3_2 h)

/-- Cross-consistency: all three agree on input bits. -/
theorem checkSboxFull_bits_consistent (cert : SboxFullCert) (sbox : SboxTable)
    (h : checkSboxFull cert sbox = true) :
    cert.ddtCert.inputBits = sbox.inputBits ∧
    cert.latCert.inputBits = sbox.inputBits ∧
    cert.algDegreeCert.inputBits = sbox.inputBits := by
  unfold checkSboxFull at h
  exact ⟨checkDDT_bits cert.ddtCert sbox (full_and3_1 h),
         checkLAT_bits cert.latCert sbox (full_and3_2 h),
         checkAlgDegree_bits cert.algDegreeCert sbox (full_and3_3 h)⟩

/-! ## Bridge to SboxAnalysis

Extract an SboxAnalysis from a verified full certificate. -/

/-- Build SboxAnalysis from verified full certificate.
    Uses certified values instead of recomputation. -/
def sboxAnalysisFromCert (cert : SboxFullCert) (sbox : SboxTable)
    (h : checkSboxFull cert sbox = true) : SboxAnalysis where
  inputBits := sbox.inputBits
  diffUniformity := cert.ddtCert.maxDelta
  nonlinearity := cert.latCert.nonlinearity
  algebraicDeg := cert.algDegreeCert.degree
  maxWalsh := cert.latCert.maxBias
  h_delta_le := by
    rw [checkSboxFull_ddt_sound cert sbox h]
    exact diffUniformity_le sbox
  h_deg_le := by
    rw [checkSboxFull_algdeg_sound cert sbox h]
    exact algebraicDegreeFromTable_le sbox

/-- Certified analysis matches standard analysis on all fields. -/
theorem sboxAnalysisFromCert_eq (cert : SboxFullCert) (sbox : SboxTable)
    (h : checkSboxFull cert sbox = true) :
    (sboxAnalysisFromCert cert sbox h).diffUniformity =
    (analyzeSbox sbox).diffUniformity ∧
    (sboxAnalysisFromCert cert sbox h).nonlinearity =
    (analyzeSbox sbox).nonlinearity ∧
    (sboxAnalysisFromCert cert sbox h).algebraicDeg =
    (analyzeSbox sbox).algebraicDeg := by
  unfold sboxAnalysisFromCert analyzeSbox
  simp only []
  exact ⟨checkSboxFull_ddt_sound cert sbox h,
         checkSboxFull_nl_sound cert sbox h,
         checkSboxFull_algdeg_sound cert sbox h⟩

/-! ## Concrete Full Certificates -/

/-- Full certificate for PRESENT S-box. -/
def presentFullCert : SboxFullCert :=
  { ddtCert := presentDDTCert
    latCert := presentLATCert
    algDegreeCert := presentAlgDegreeCert }

/-- PRESENT full certificate is valid. -/
theorem present_full_valid : checkSboxFull presentFullCert presentSbox = true := by
  native_decide

/-- PRESENT certified analysis matches standalone analysis. -/
theorem present_certified_consistent :
    (sboxAnalysisFromCert presentFullCert presentSbox present_full_valid).diffUniformity =
    (analyzeSbox presentSbox).diffUniformity := by
  native_decide

/-- Full certificate for toy 2-bit S-box. -/
def toy2FullCert : SboxFullCert :=
  { ddtCert := toy2DDTCert
    latCert := toy2LATCert
    algDegreeCert := toy2AlgDegreeCert }

/-- Toy 2-bit full certificate is valid. -/
theorem toy2_full_valid : checkSboxFull toy2FullCert toy2Sbox = true := by
  native_decide

/-- Full certificate for toy 3-bit S-box. -/
def toy3FullCert : SboxFullCert :=
  { ddtCert := toy3DDTCert
    latCert := toy3LATCert
    algDegreeCert := toy3AlgDegreeCert }

/-- Toy 3-bit full certificate is valid. -/
theorem toy3_full_valid : checkSboxFull toy3FullCert toy3Sbox = true := by
  native_decide

end SuperHash.Sbox.SboxFullCert
