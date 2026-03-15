-- SuperHash/Sbox/LATCompute.lean
-- Compute Linear Approximation Table from concrete S-box
-- LAT[a][b] = sum_x (-1)^{<a,x> XOR <b,S(x)>} (Walsh-Hadamard coefficient)
-- Nonlinearity NL(S) = (2^n - max_{a!=0,b!=0} |LAT[a][b]|) / 2
-- Adapted from TrustHash/Sbox/LATCompute.lean for Lean 4.28

import SuperHash.Sbox.SboxTable
import SuperHash.Sbox.FinIter

namespace SuperHash.Sbox.LATCompute

open SuperHash.Sbox
open SuperHash.Sbox.Bitwise
open SuperHash.Sbox.FinIter

/-! ## LAT computation

The Linear Approximation Table (LAT) of S : {0,1}^n -> {0,1}^n has entry
  LAT[a][b] = sum_x (-1)^{<a,x> XOR <b,S(x)>}
where <.,.> is the inner product over GF(2).

We compute |LAT[a][b]| = |2*matchCount - 2^n| where
  matchCount = |{x : <a,x> = <b,S(x)>}|.

Nonlinearity NL(S) = (2^n - max_{a!=0,b!=0} |LAT[a][b]|) / 2.
- PRESENT 4-bit S-box: NL = 4
- Affine S-box: NL = 0 (worst case) -/

/-- Count inputs where masks a,b give matching parities: <a,x> = <b,S(x)>.
    This is the "match count" underlying LAT entry (a,b). -/
def latMatchCount (s : SboxTable) (a b : Nat) : Nat :=
  let N := 2 ^ s.inputBits
  let n := s.inputBits
  (List.range N).foldl (fun acc x =>
    if innerParity a x n == innerParity b (s.eval x) n then acc + 1 else acc) 0

/-- Absolute Walsh coefficient: |LAT[a][b]| = |2*matchCount - 2^n|. -/
def walshAbs (s : SboxTable) (a b : Nat) : Nat :=
  let N := 2 ^ s.inputBits
  let c := latMatchCount s a b
  if 2 * c ≥ N then 2 * c - N else N - 2 * c

/-- Maximum Walsh bias over non-trivial masks: max_{a!=0,b!=0} |LAT[a][b]|. -/
def maxWalshBias (s : SboxTable) : Nat :=
  let N := 2 ^ s.inputBits
  maxOverNonzero N (fun a => maxOverNonzero N (fun b => walshAbs s a b))

/-- Nonlinearity: NL(S) = (2^n - max|LAT|) / 2. -/
def nonlinearityFromTable (s : SboxTable) : Nat :=
  (2 ^ s.inputBits - maxWalshBias s) / 2

/-- Full LAT as match counts. LAT[a][b] for a, b in [0, 2^n). -/
def computeLAT (s : SboxTable) : Array (Array Nat) :=
  tabulate2D (2 ^ s.inputBits) (2 ^ s.inputBits) (fun a b => latMatchCount s a b)

/-! ## Bounds -/

private theorem foldl_count_le (l : List Nat) (f : Nat → Bool) (acc : Nat) :
    l.foldl (fun acc x => if f x then acc + 1 else acc) acc ≤ l.length + acc := by
  induction l generalizing acc with
  | nil => simp [List.foldl]
  | cons x xs ih =>
    simp [List.foldl]; split
    · have := ih (acc + 1); omega
    · have := ih acc; omega

theorem latMatchCount_le (s : SboxTable) (a b : Nat) :
    latMatchCount s a b ≤ 2 ^ s.inputBits := by
  unfold latMatchCount
  simp only []
  have h := foldl_count_le (List.range (2 ^ s.inputBits))
    (fun x => innerParity a x s.inputBits == innerParity b (s.eval x) s.inputBits) 0
  rw [List.length_range] at h; omega

theorem walshAbs_le (s : SboxTable) (a b : Nat) :
    walshAbs s a b ≤ 2 ^ s.inputBits := by
  unfold walshAbs
  simp only []
  have hc := latMatchCount_le s a b
  split <;> omega

/-- Maximum Walsh bias is bounded by 2^n. -/
theorem maxWalshBias_le (s : SboxTable) :
    maxWalshBias s ≤ 2 ^ s.inputBits := by
  unfold maxWalshBias
  simp only []
  have inner_le : ∀ a, maxOverNonzero (2 ^ s.inputBits) (fun b => walshAbs s a b) ≤ 2 ^ s.inputBits :=
    fun a => maxOverNonzero_le_bound _ _ _ (fun i _ => walshAbs_le s a i)
  exact maxOverNonzero_le_bound _ _ _ (fun i _ => inner_le i)

/-- LAT table size equals domain size. -/
theorem computeLAT_size (s : SboxTable) :
    (computeLAT s).size = 2 ^ s.inputBits := by
  unfold computeLAT; exact tabulate2D_size _ _ _

/-! ## Concrete validation -/

/-- PRESENT S-box has nonlinearity NL = 4.
    Reference: Bogdanov et al. 2007. -/
theorem present_nonlinearity :
    nonlinearityFromTable presentSbox = 4 := by native_decide

/-- Toy 2-bit swap S-box is affine, NL = 0. -/
theorem toy2_nonlinearity :
    nonlinearityFromTable toy2Sbox = 0 := by native_decide

/-- Toy 3-bit cyclic shift has NL = 0 (quasi-linear). -/
theorem toy3_nonlinearity :
    nonlinearityFromTable toy3Sbox = 0 := by native_decide

/-- All masks zero gives matchCount = 2^n (trivial). -/
theorem present_lat_0_0 : latMatchCount presentSbox 0 0 = 16 := by native_decide

/-- Walsh coefficient |LAT[1][5]| for PRESENT = 8 (maximum bias). -/
theorem present_walsh_1_5 : walshAbs presentSbox 1 5 = 8 := by native_decide

/-- Maximum Walsh bias for PRESENT = 8. -/
theorem present_maxWalsh : maxWalshBias presentSbox = 8 := by native_decide

end SuperHash.Sbox.LATCompute
