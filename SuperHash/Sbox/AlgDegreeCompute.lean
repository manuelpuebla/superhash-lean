-- SuperHash/Sbox/AlgDegreeCompute.lean
-- Compute algebraic degree from concrete S-box via Moebius transform
-- ANF: f(x) = XOR_u a_u * x^u where a_u = XOR_{v subset u} f(v)
-- Degree = max weight(u) where a_u != 0
-- Adapted from TrustHash/Sbox/AlgDegreeCompute.lean for Lean 4.28

import SuperHash.Sbox.SboxTable
import SuperHash.Sbox.FinIter

namespace SuperHash.Sbox.AlgDegreeCompute

open SuperHash.Sbox
open SuperHash.Sbox.Bitwise
open SuperHash.Sbox.FinIter

/-! ## Algebraic Normal Form (ANF) via Moebius Transform

For a Boolean function f: {0,1}^n -> {0,1}, the ANF coefficients are:
  a_u = XOR_{v : v AND u = v} f(v)  (XOR over all submasks of u)

The algebraic degree = max{wt(u) : a_u != 0}.

For S: {0,1}^n -> {0,1}^n, decompose into n coordinate functions:
  S_j(x) = bit j of S(x)
  algDeg(S) = max_j algDeg(S_j)

- PRESENT 4-bit S-box: degree 3
- Affine S-box: degree 1
- Identity S-box: degree 1 -/

/-- Bit j of S(x): the j-th coordinate function value at x. -/
def coordBit (s : SboxTable) (j x : Nat) : Nat :=
  if (s.eval x).testBit j then 1 else 0

/-- Moebius coefficient a_u for coordinate function j.
    a_u = XOR_{v submask of u} coordBit(j, v). -/
def moebiusCoeff (s : SboxTable) (j u : Nat) : Nat :=
  let N := 2 ^ s.inputBits
  (List.range N).foldl (fun acc v =>
    if Nat.land v u == v then xorNat acc (coordBit s j v) else acc) 0

/-- Algebraic degree of coordinate function j:
    max Hamming weight of nonzero ANF monomial. -/
def algDegreeCoord (s : SboxTable) (j : Nat) : Nat :=
  let N := 2 ^ s.inputBits
  (List.range N).foldl (fun maxDeg u =>
    if moebiusCoeff s j u != 0
    then Nat.max maxDeg (popcount u s.inputBits)
    else maxDeg) 0

/-- Algebraic degree of S-box: max over all coordinate functions. -/
def algebraicDegreeFromTable (s : SboxTable) : Nat :=
  maxOver s.inputBits (fun j => algDegreeCoord s j)

/-! ## Bounds -/

theorem algDegreeCoord_le (s : SboxTable) (j : Nat) :
    algDegreeCoord s j ≤ s.inputBits := by
  unfold algDegreeCoord
  simp only []
  suffices ∀ (l : List Nat) (acc : Nat), acc ≤ s.inputBits →
    l.foldl (fun maxDeg u =>
      if moebiusCoeff s j u != 0
      then Nat.max maxDeg (popcount u s.inputBits)
      else maxDeg) acc ≤ s.inputBits by
    exact this (List.range (2 ^ s.inputBits)) 0 (Nat.zero_le _)
  intro l acc hacc
  induction l generalizing acc with
  | nil => simp [List.foldl]; exact hacc
  | cons x xs ih =>
    simp only [List.foldl]; split
    · apply ih; exact Nat.max_le.mpr ⟨hacc, popcount_le_maxBit x s.inputBits⟩
    · exact ih acc hacc

/-- Algebraic degree of S-box is bounded by input bits. -/
theorem algebraicDegreeFromTable_le (s : SboxTable) :
    algebraicDegreeFromTable s ≤ s.inputBits := by
  unfold algebraicDegreeFromTable
  exact maxOver_le_bound _ _ _ (fun i _ => algDegreeCoord_le s i)

/-! ## Concrete validation -/

/-- PRESENT S-box has algebraic degree 3.
    Reference: Bogdanov et al. 2007. -/
theorem present_algDegree :
    algebraicDegreeFromTable presentSbox = 3 := by native_decide

/-- Toy 2-bit swap [1,0,3,2] is affine, degree = 1. -/
theorem toy2_algDegree :
    algebraicDegreeFromTable toy2Sbox = 1 := by native_decide

/-- Toy 3-bit cyclic shift [1,2,3,4,5,6,7,0] has degree 2. -/
theorem toy3_algDegree :
    algebraicDegreeFromTable toy3Sbox = 2 := by native_decide

/-- PRESENT coordinate 1 has degree 3 (the maximum). -/
theorem present_coord1_degree :
    algDegreeCoord presentSbox 1 = 3 := by native_decide

/-- PRESENT monomial x0x1x2 (u=7, weight 3) is nonzero for coord 1. -/
theorem present_moebius_1_7 :
    moebiusCoeff presentSbox 1 7 = 1 := by native_decide

end SuperHash.Sbox.AlgDegreeCompute
