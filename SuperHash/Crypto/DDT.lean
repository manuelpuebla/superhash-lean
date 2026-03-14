import SuperHash.Crypto.Semantics

/-!
# SuperHash.Crypto.DDT — Difference Distribution Table computation

v2.5 Phase 2: Computes DDT and differential uniformity of concrete S-boxes.
Uses functional style (List.countP, List.foldl) for Lean 4 compatibility.

NOTE: CertifiedSbox currently covers PRESENT (4-bit, 16 entries).
AES (8-bit, 256 entries) DDT computation is feasible via native_decide
but requires the full 256-entry lookup table. Poseidon operates over
prime fields (not GF(2^n)) so DDT is not directly applicable.
-/

namespace SuperHash

-- ============================================================
-- Section 1: Concrete S-box as Array
-- ============================================================

/-- A concrete S-box as an Array of Nat values. -/
structure ConcreteSbox where
  bits : Nat
  table : Array Nat
  h_size : table.size = 2 ^ bits

/-- PRESENT 4-bit S-box. -/
def presentSbox : ConcreteSbox where
  bits := 4
  table := #[12, 5, 6, 11, 9, 0, 10, 13, 3, 14, 15, 8, 4, 7, 1, 2]
  h_size := by native_decide

/-- S-box lookup with bounds fallback. -/
def ConcreteSbox.apply (sbox : ConcreteSbox) (x : Nat) : Nat :=
  if h : x < sbox.table.size then sbox.table[x] else 0

-- ============================================================
-- Section 2: DDT computation (functional)
-- ============================================================

/-- Count #{x ∈ [0, 2^n) : S(x ⊕ a) ⊕ S(x) = b}. -/
def ddtEntry (sbox : ConcreteSbox) (a b : Nat) : Nat :=
  (List.range (2 ^ sbox.bits)).countP fun x =>
    (sbox.apply (x ^^^ a) ^^^ sbox.apply x) == b

/-- Compute δ = max_{a≠0, b} DDT(a,b). -/
def diffUniformity (sbox : ConcreteSbox) : Nat :=
  let size := 2 ^ sbox.bits
  (List.range size).foldl (fun acc a =>
    if a == 0 then acc
    else (List.range size).foldl (fun acc2 b =>
      max acc2 (ddtEntry sbox a b)) acc
  ) 0

-- ============================================================
-- Section 3: Concrete verification
-- ============================================================

-- PRESENT S-box differential uniformity
#eval diffUniformity presentSbox

-- Sample DDT entries
#eval ddtEntry presentSbox 1 0
#eval ddtEntry presentSbox 1 6
#eval ddtEntry presentSbox 0 0   -- 16 (trivial row)

-- S-box correctness
#eval presentSbox.apply 0   -- 12
#eval presentSbox.apply 5   -- 0
#eval presentSbox.apply 15  -- 2

-- ============================================================
-- Section 4: CertifiedSbox
-- ============================================================

/-- S-box with verified δ. -/
structure CertifiedSbox extends ConcreteSbox where
  delta : Nat
  h_delta : delta = diffUniformity toConcreteSbox

/-- PRESENT certified. -/
def presentCertified : CertifiedSbox where
  bits := 4
  table := #[12, 5, 6, 11, 9, 0, 10, 13, 3, 14, 15, 8, 4, 7, 1, 2]
  h_size := by native_decide
  delta := 4
  h_delta := by native_decide

/-- Convert to SboxParams. -/
def CertifiedSbox.toSboxParams (cs : CertifiedSbox) (deg nl : Nat)
    (h_bits : cs.bits ≥ 1) (h_deg : deg ≥ 1) (h_du : cs.delta ≥ 2) : SboxParams where
  inputBits := cs.bits
  diffUniformity := cs.delta
  nonlinearity := nl
  algebraicDeg := deg
  h_bits := h_bits
  h_du_pos := h_du
  h_deg_pos := h_deg

/-- PRESENT params from certification. -/
def presentParams : SboxParams :=
  presentCertified.toSboxParams 3 4 (by native_decide) (by omega) (by native_decide)

-- ============================================================
-- Section 5: Security from certified S-box
-- ============================================================

/-- Security bits = activeSboxes × (n - log2(δ)). -/
def certSecurityBits (cs : CertifiedSbox) (activeSboxes : Nat) : Nat :=
  activeSboxes * (cs.bits - Nat.log2 cs.delta)

#eval certSecurityBits presentCertified 75  -- 150

/-- Security monotone. -/
theorem certSecurity_monotone (cs : CertifiedSbox) (a1 a2 : Nat) (h : a1 ≤ a2) :
    certSecurityBits cs a1 ≤ certSecurityBits cs a2 :=
  Nat.mul_le_mul_right _ h

-- ============================================================
-- Section 6: Non-vacuity
-- ============================================================

example : presentCertified.delta = 4 := rfl
example : certSecurityBits presentCertified 75 = 150 := by native_decide
example : presentSbox.apply 0 = 12 := by native_decide
example : presentSbox.apply 5 = 0 := by native_decide

end SuperHash
