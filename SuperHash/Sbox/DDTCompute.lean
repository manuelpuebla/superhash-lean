-- SuperHash/Sbox/DDTCompute.lean
-- Compute Differential Distribution Table from concrete S-box
-- DDT[a][b] = |{x in [0, 2^n) : S(x XOR a) XOR S(x) = b}|
-- Adapted from TrustHash/Sbox/DDTCompute.lean for Lean 4.28

import SuperHash.Sbox.SboxTable
import SuperHash.Sbox.FinIter

namespace SuperHash.Sbox.DDTCompute

open SuperHash.Sbox
open SuperHash.Sbox.Bitwise
open SuperHash.Sbox.FinIter

/-! ## DDT computation

The Differential Distribution Table (DDT) of an S-box S : {0,1}^n -> {0,1}^n
has entry DDT[a][b] = |{x in {0,...,2^n-1} : S(x XOR a) XOR S(x) = b}|.

The differential uniformity delta(S) = max_{a != 0, b} DDT[a][b].
- APN (Almost Perfect Nonlinear): delta = 2 (optimal for odd n)
- PRESENT 4-bit S-box: delta = 4
- Affine S-box: delta = 2^n (maximum, worst case) -/

/-- Count how many x in [0, 2^n) give output difference b for input difference a.
    This is DDT[a][b]. Complexity: O(2^n) per entry. -/
def ddtEntry (s : SboxTable) (a b : Nat) : Nat :=
  let N := 2 ^ s.inputBits
  (List.range N).foldl (fun acc x =>
    let outDiff := xorNat (s.eval (xorNat x a % N)) (s.eval (x % N))
    if outDiff == b then acc + 1 else acc
  ) 0

/-- Maximum DDT entry over all output differences, for fixed input difference a.
    This is max_b DDT[a][b]. -/
def maxDDTRow (s : SboxTable) (a : Nat) : Nat :=
  maxOver (2 ^ s.inputBits) (fun b => ddtEntry s a b)

/-- Differential uniformity: max_{a != 0} max_b DDT[a][b].
    This is THE key S-box security parameter delta. -/
def diffUniformityFromTable (s : SboxTable) : Nat :=
  maxOverNonzero (2 ^ s.inputBits) (fun a => maxDDTRow s a)

/-- Compute the full DDT as a 2D array. DDT[a][b] for a, b in [0, 2^n). -/
def computeDDT (s : SboxTable) : Array (Array Nat) :=
  tabulate2D (2 ^ s.inputBits) (2 ^ s.inputBits) (fun a b => ddtEntry s a b)

/-! ## DDT entry bound

Each DDT entry counts elements from a domain of size 2^n. -/

private theorem foldl_count_le (l : List Nat) (f : Nat → Bool) (acc : Nat) :
    l.foldl (fun acc x => if f x then acc + 1 else acc) acc ≤ l.length + acc := by
  induction l generalizing acc with
  | nil => simp [List.foldl]
  | cons x xs ih =>
    simp [List.foldl]
    split
    · have := ih (acc + 1); omega
    · have := ih acc; omega

theorem ddtEntry_le (s : SboxTable) (a b : Nat) :
    ddtEntry s a b ≤ 2 ^ s.inputBits := by
  unfold ddtEntry
  simp only []  -- beta-reduce let bindings
  have h := foldl_count_le (List.range (2 ^ s.inputBits))
    (fun x => xorNat (s.eval (xorNat x a % 2 ^ s.inputBits))
                      (s.eval (x % 2 ^ s.inputBits)) == b) 0
  rw [List.length_range] at h; omega

/-- maxDDTRow is bounded by 2^n. -/
theorem maxDDTRow_le (s : SboxTable) (a : Nat) :
    maxDDTRow s a ≤ 2 ^ s.inputBits := by
  unfold maxDDTRow
  exact maxOver_le_bound _ _ _ (fun i _ => ddtEntry_le s a i)

/-- Differential uniformity is bounded by 2^n. -/
theorem diffUniformity_le (s : SboxTable) :
    diffUniformityFromTable s ≤ 2 ^ s.inputBits := by
  unfold diffUniformityFromTable maxOverNonzero
  suffices ∀ (l : List Nat) (acc : Nat), acc ≤ 2 ^ s.inputBits →
    l.foldl (fun acc i => if i == 0 then acc else Nat.max acc (maxDDTRow s i)) acc ≤
    2 ^ s.inputBits by
    exact this (List.range (2 ^ s.inputBits)) 0 (Nat.zero_le _)
  intro l acc hacc
  induction l generalizing acc with
  | nil => simp [List.foldl]; exact hacc
  | cons x xs ih =>
    simp only [List.foldl]
    split
    · exact ih acc hacc
    · exact ih _ (Nat.max_le.mpr ⟨hacc, maxDDTRow_le s x⟩)

/-- DDT size equals domain size squared. -/
theorem computeDDT_size (s : SboxTable) :
    (computeDDT s).size = 2 ^ s.inputBits := by
  unfold computeDDT; exact tabulate2D_size _ _ _

/-! ## Concrete validation -- THE critical tests

These native_decide proofs verify that our DDT computation matches
known cryptanalytic results from the literature. -/

/-- PRESENT S-box has differential uniformity delta = 4.
    Reference: Bogdanov et al. 2007. -/
theorem present_diffUniformity :
    diffUniformityFromTable presentSbox = 4 := by native_decide

/-- Toy 2-bit swap S-box [1,0,3,2] has delta = 4 (= 2^2, affine -> maximum). -/
theorem toy2_diffUniformity :
    diffUniformityFromTable toy2Sbox = 4 := by native_decide

/-- Toy 3-bit cyclic shift S-box [1,2,3,4,5,6,7,0] has delta = 8 (= 2^3, linear). -/
theorem toy3_diffUniformity :
    diffUniformityFromTable toy3Sbox = 8 := by native_decide

/-- DDT entry spot-check: DDT[1][9] for PRESENT = 4. -/
theorem present_ddt_1_9 : ddtEntry presentSbox 1 9 = 4 := by native_decide

/-- DDT entry spot-check: DDT[0][b] = 0 for b != 0 (identity difference). -/
theorem present_ddt_0_5 : ddtEntry presentSbox 0 5 = 0 := by native_decide

/-- DDT entry spot-check: DDT[0][0] = 2^n = 16 (all x give zero output diff). -/
theorem present_ddt_0_0 : ddtEntry presentSbox 0 0 = 16 := by native_decide

/-- Differential uniformity correctly excludes row 0:
    maxDDTRow for a=0 is 16 (trivial), but diffUniformity is 4 (excludes a=0). -/
theorem present_row0_max : maxDDTRow presentSbox 0 = 16 := by native_decide

end SuperHash.Sbox.DDTCompute
