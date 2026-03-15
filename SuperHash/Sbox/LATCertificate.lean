-- SuperHash/Sbox/LATCertificate.lean
-- LAT Certificate: verify claimed nonlinearity and max bias for S-boxes
-- Pattern: certificate oracle (structure + Bool checker + soundness theorems)
-- Adapted from TrustHash/Sbox/LATCertificate.lean for Lean 4.28

import SuperHash.Sbox.LATCompute
import SuperHash.Sbox.SboxTable

namespace SuperHash.Sbox.LATCertificate

open SuperHash.Sbox
open SuperHash.Sbox.LATCompute

/-! ## LAT Certificate Structure

A LAT certificate packages a claimed maximum Walsh bias and nonlinearity
for an S-box of a given bit width. Produced offline, verified in Lean.

Design mirrors DDTCertificate: minimal data, all verification by checker. -/

/-- A LAT certificate packages claimed max Walsh bias and nonlinearity
    for an S-box of a given bit width. -/
structure LATCertificate where
  /-- Bit width of the S-box -/
  inputBits : Nat
  /-- Claimed maximum Walsh bias: max_{a!=0,b!=0} |LAT[a][b]| -/
  maxBias : Nat
  /-- Claimed nonlinearity: (2^n - maxBias) / 2 -/
  nonlinearity : Nat
  deriving Repr, DecidableEq

/-! ## Bool Checker -/

/-- Check a LAT certificate against an S-box by full recomputation.
    Returns true iff bit widths match AND maxBias equals the
    actual computed maximum Walsh bias AND nonlinearity matches. -/
def checkLAT (cert : LATCertificate) (sbox : SboxTable) : Bool :=
  cert.inputBits == sbox.inputBits &&
  cert.maxBias == maxWalshBias sbox &&
  cert.nonlinearity == nonlinearityFromTable sbox

/-! ## Soundness Theorems -/

private theorem and3_1 {a b c : Bool} (h : (a && b && c) = true) : a = true := by
  cases a <;> simp_all

private theorem and3_2 {a b c : Bool} (h : (a && b && c) = true) : b = true := by
  cases a <;> cases b <;> simp_all

private theorem and3_3 {a b c : Bool} (h : (a && b && c) = true) : c = true := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- **Soundness**: if the checker passes, maxBias equals the actual
    maximum Walsh bias. This is THE key theorem of the LAT certificate. -/
theorem checkLAT_sound (cert : LATCertificate) (sbox : SboxTable)
    (h : checkLAT cert sbox = true) :
    cert.maxBias = maxWalshBias sbox := by
  unfold checkLAT at h
  exact eq_of_beq (and3_2 h)

/-- **Bit width soundness**: if checker passes, input bits match. -/
theorem checkLAT_bits (cert : LATCertificate) (sbox : SboxTable)
    (h : checkLAT cert sbox = true) :
    cert.inputBits = sbox.inputBits := by
  unfold checkLAT at h
  exact eq_of_beq (and3_1 h)

/-- **Nonlinearity soundness**: if checker passes, nonlinearity matches. -/
theorem checkLAT_nl (cert : LATCertificate) (sbox : SboxTable)
    (h : checkLAT cert sbox = true) :
    cert.nonlinearity = nonlinearityFromTable sbox := by
  unfold checkLAT at h
  exact eq_of_beq (and3_3 h)

/-- **Upper bound**: certified max bias is bounded by 2^n. -/
theorem checkLAT_upper_bound (cert : LATCertificate) (sbox : SboxTable)
    (h : checkLAT cert sbox = true) :
    cert.maxBias ≤ 2 ^ sbox.inputBits := by
  rw [checkLAT_sound cert sbox h]
  exact maxWalshBias_le sbox

/-! ## Extraction -/

/-- Extract certified max bias from a valid certificate. -/
def certifiedMaxBias (cert : LATCertificate) (sbox : SboxTable)
    (_ : checkLAT cert sbox = true) : Nat :=
  cert.maxBias

/-- Extract certified nonlinearity from a valid certificate. -/
def certifiedNonlinearity (cert : LATCertificate) (sbox : SboxTable)
    (_ : checkLAT cert sbox = true) : Nat :=
  cert.nonlinearity

/-- Certified max bias equals actual max Walsh bias. -/
theorem certifiedMaxBias_eq (cert : LATCertificate) (sbox : SboxTable)
    (h : checkLAT cert sbox = true) :
    certifiedMaxBias cert sbox h = maxWalshBias sbox := by
  unfold certifiedMaxBias
  exact checkLAT_sound cert sbox h

/-- Certified nonlinearity equals actual nonlinearity. -/
theorem certifiedNonlinearity_eq (cert : LATCertificate) (sbox : SboxTable)
    (h : checkLAT cert sbox = true) :
    certifiedNonlinearity cert sbox h = nonlinearityFromTable sbox := by
  unfold certifiedNonlinearity
  exact checkLAT_nl cert sbox h

/-! ## Rejection Theorems -/

/-- Wrong bit width is rejected. -/
theorem wrong_bits_rejected :
    checkLAT ⟨3, 8, 4⟩ presentSbox = false := by native_decide

/-- Wrong maxBias is rejected. -/
theorem wrong_bias_rejected :
    checkLAT ⟨4, 10, 4⟩ presentSbox = false := by native_decide

/-- Wrong nonlinearity is rejected. -/
theorem wrong_nl_rejected :
    checkLAT ⟨4, 8, 5⟩ presentSbox = false := by native_decide

/-- Zero bias is rejected for non-trivial S-box. -/
theorem zero_bias_rejected :
    checkLAT ⟨4, 0, 8⟩ presentSbox = false := by native_decide

/-! ## Concrete Certificates -/

/-- LAT certificate for PRESENT S-box: maxBias = 8, NL = 4. -/
def presentLATCert : LATCertificate :=
  { inputBits := 4, maxBias := 8, nonlinearity := 4 }

/-- PRESENT LAT certificate is valid. -/
theorem present_lat_valid : checkLAT presentLATCert presentSbox = true := by native_decide

/-- PRESENT certified max bias. -/
theorem present_lat_bias :
    certifiedMaxBias presentLATCert presentSbox present_lat_valid = 8 := rfl

/-- PRESENT certified nonlinearity. -/
theorem present_lat_nl :
    certifiedNonlinearity presentLATCert presentSbox present_lat_valid = 4 := rfl

/-- LAT certificate for toy 2-bit S-box: maxBias = 4, NL = 0 (affine). -/
def toy2LATCert : LATCertificate :=
  { inputBits := 2, maxBias := 4, nonlinearity := 0 }

/-- Toy 2-bit LAT certificate is valid. -/
theorem toy2_lat_valid : checkLAT toy2LATCert toy2Sbox = true := by native_decide

/-- LAT certificate for toy 3-bit S-box: maxBias = 8, NL = 0. -/
def toy3LATCert : LATCertificate :=
  { inputBits := 3, maxBias := 8, nonlinearity := 0 }

/-- Toy 3-bit LAT certificate is valid. -/
theorem toy3_lat_valid : checkLAT toy3LATCert toy3Sbox = true := by native_decide

/-! ## Cross-validation -/

/-- The NL from LAT certificate matches the standalone computation. -/
theorem lat_nl_consistent :
    presentLATCert.nonlinearity = nonlinearityFromTable presentSbox := by native_decide

end SuperHash.Sbox.LATCertificate
