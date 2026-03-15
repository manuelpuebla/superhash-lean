-- SuperHash/Sbox/FinIter.lean
-- Finite iteration utilities without Mathlib Finset
-- Foundation for S-box DDT/LAT computation
-- Adapted from TrustHash/FinIter.lean for Lean 4.28

namespace SuperHash.Sbox.FinIter

/-! ## Range generation

Build arrays of all values in a range, used for iterating over
S-box inputs (Fin 2^n) represented as Nat. -/

/-- Array of all naturals from 0 to n-1. -/
def rangeArray (n : Nat) : Array Nat :=
  (List.range n).toArray

theorem rangeArray_size (n : Nat) : (rangeArray n).size = n := by
  unfold rangeArray
  rw [List.size_toArray, List.length_range]

/-- All Nat values less than n, as a List. -/
def allNatsBelow (n : Nat) : List Nat := List.range n

theorem allNatsBelow_length (n : Nat) : (allNatsBelow n).length = n := by
  unfold allNatsBelow; exact List.length_range

theorem mem_allNatsBelow (n k : Nat) : k ∈ allNatsBelow n ↔ k < n := by
  unfold allNatsBelow; exact List.mem_range

/-! ## Fold-based aggregation

Replace Finset.sup / Finset.sum with foldl over explicit ranges. -/

/-- Maximum of f(i) for i in 0..n-1. Returns 0 if n = 0. -/
def maxOver (n : Nat) (f : Nat → Nat) : Nat :=
  (List.range n).foldl (fun acc i => Nat.max acc (f i)) 0

/-- Maximum of f(i) for i in 1..n-1 (excludes 0). Returns 0 if n ≤ 1.
    Used for DDT where delta_in = 0 is excluded. -/
def maxOverNonzero (n : Nat) (f : Nat → Nat) : Nat :=
  (List.range n).foldl (fun acc i => if i == 0 then acc else Nat.max acc (f i)) 0

/-- Minimum of f(i) for i in 0..n-1. Returns default if n = 0. -/
def minOver (n : Nat) (f : Nat → Nat) (default : Nat) : Nat :=
  (List.range n).foldl (fun acc i => Nat.min acc (f i)) default

/-- Index achieving the minimum of f over 0..n-1. Returns 0 if n = 0. -/
def argMin (n : Nat) (f : Nat → Nat) : Nat :=
  if n == 0 then 0
  else
    let result := (List.range n).foldl (fun (best : Nat × Nat) i =>
      let v := f i
      if v < best.2 then (i, v) else best
    ) (0, f 0)
    result.1

/-- Sum of f(i) for i in 0..n-1. -/
def sumOver (n : Nat) (f : Nat → Nat) : Nat :=
  (List.range n).foldl (fun acc i => acc + f i) 0

/-- Count how many i in 0..n-1 satisfy predicate p. -/
def countOver (n : Nat) (p : Nat → Bool) : Nat :=
  (List.range n).foldl (fun acc i => if p i then acc + 1 else acc) 0

/-! ## Auxiliary foldl lemmas -/

private theorem foldl_max_ge_init (l : List Nat) (f : Nat → Nat) (init : Nat) :
    init ≤ l.foldl (fun acc i => Nat.max acc (f i)) init := by
  induction l generalizing init with
  | nil => simp [List.foldl]
  | cons x xs ih =>
    simp [List.foldl]
    calc init ≤ Nat.max init (f x) := Nat.le_max_left init (f x)
    _ ≤ xs.foldl (fun acc i => Nat.max acc (f i)) (Nat.max init (f x)) := ih _

private theorem foldl_max_le (l : List Nat) (f : Nat → Nat) (acc : Nat) (bound : Nat)
    (hacc : acc ≤ bound) (hall : ∀ x, x ∈ l → f x ≤ bound) :
    l.foldl (fun acc i => Nat.max acc (f i)) acc ≤ bound := by
  induction l generalizing acc with
  | nil => simp [List.foldl]; exact hacc
  | cons x xs ih =>
    simp [List.foldl]
    apply ih
    · exact Nat.max_le.mpr ⟨hacc, hall x List.mem_cons_self⟩
    · intro y hy; exact hall y (List.mem_cons_of_mem x hy)

/-! ## Properties of maxOver -/

theorem maxOver_le_bound (n : Nat) (f : Nat → Nat) (bound : Nat)
    (h : ∀ i, i < n → f i ≤ bound) : maxOver n f ≤ bound := by
  unfold maxOver
  apply foldl_max_le
  · omega
  · intro x hx; exact h x (List.mem_range.mp hx)

theorem maxOver_ge_at (n : Nat) (f : Nat → Nat) (k : Nat) (hk : k < n) :
    f k ≤ maxOver n f := by
  unfold maxOver
  suffices ∀ (l : List Nat) (init : Nat),
    k ∈ l → f k ≤ l.foldl (fun acc i => Nat.max acc (f i)) init by
    exact this (List.range n) 0 (List.mem_range.mpr hk)
  intro l init hmem
  induction l generalizing init with
  | nil => exact absurd hmem List.not_mem_nil
  | cons x xs ih =>
    simp [List.foldl]
    cases List.mem_cons.mp hmem with
    | inl heq =>
      subst heq
      calc f k ≤ Nat.max init (f k) := Nat.le_max_right init (f k)
      _ ≤ xs.foldl (fun acc i => Nat.max acc (f i)) (Nat.max init (f k)) :=
        foldl_max_ge_init xs f _
    | inr hmem => exact ih (init := Nat.max init (f x)) hmem

/-! ## Properties of countOver -/

theorem countOver_le (n : Nat) (p : Nat → Bool) : countOver n p ≤ n := by
  unfold countOver
  suffices ∀ (l : List Nat) (acc : Nat),
    l.foldl (fun acc i => if p i then acc + 1 else acc) acc ≤ l.length + acc by
    have := this (List.range n) 0
    rw [List.length_range] at this; omega
  intro l acc
  induction l generalizing acc with
  | nil => simp [List.foldl]
  | cons x xs ih =>
    simp [List.foldl]; split
    · have := ih (acc + 1); omega
    · have := ih acc; omega

/-! ## 2D iteration

For DDT/LAT: iterate over all (a, x) pairs in [0, 2^n) x [0, 2^n). -/

/-- Build a 2D array of size n x m by computing f(i, j) for each pair. -/
def tabulate2D (n m : Nat) (f : Nat → Nat → Nat) : Array (Array Nat) :=
  (rangeArray n).map fun i =>
    (rangeArray m).map fun j => f i j

theorem tabulate2D_size (n m : Nat) (f : Nat → Nat → Nat) :
    (tabulate2D n m f).size = n := by
  unfold tabulate2D
  rw [Array.size_map, rangeArray_size]

/-! ## Properties of maxOverNonzero -/

theorem maxOverNonzero_le_bound (n : Nat) (f : Nat → Nat) (bound : Nat)
    (h : ∀ i, i < n → f i ≤ bound) : maxOverNonzero n f ≤ bound := by
  unfold maxOverNonzero
  suffices ∀ (l : List Nat) (acc : Nat), acc ≤ bound →
    (∀ x, x ∈ l → f x ≤ bound) →
    l.foldl (fun acc i => if i == 0 then acc else Nat.max acc (f i)) acc ≤ bound by
    exact this (List.range n) 0 (Nat.zero_le _) (fun x hx => h x (List.mem_range.mp hx))
  intro l acc hacc hall
  induction l generalizing acc with
  | nil => simp [List.foldl]; exact hacc
  | cons x xs ih =>
    simp only [List.foldl]; split
    · exact ih acc hacc (fun y hy => hall y (List.mem_cons_of_mem x hy))
    · apply ih
      · exact Nat.max_le.mpr ⟨hacc, hall x List.mem_cons_self⟩
      · intro y hy; exact hall y (List.mem_cons_of_mem x hy)

/-! ## Properties of sumOver -/

private theorem foldl_sum_ge_init (l : List Nat) (f : Nat → Nat) (init : Nat) :
    init ≤ l.foldl (fun acc i => acc + f i) init := by
  induction l generalizing init with
  | nil => simp [List.foldl]
  | cons x xs ih =>
    simp [List.foldl]
    calc init ≤ init + f x := Nat.le_add_right init (f x)
    _ ≤ xs.foldl (fun acc i => acc + f i) (init + f x) := ih _

private theorem foldl_sum_le_bound (l : List Nat) (f : Nat → Nat) (bound acc : Nat)
    (hall : ∀ x, x ∈ l → f x ≤ bound) :
    l.foldl (fun acc i => acc + f i) acc ≤ bound * l.length + acc := by
  induction l generalizing acc with
  | nil => simp [List.foldl]
  | cons x xs ih =>
    simp only [List.foldl, List.length_cons]
    have hx := hall x List.mem_cons_self
    have ihres := ih (acc + f x) (fun y hy => hall y (List.mem_cons_of_mem x hy))
    have hm : bound * (xs.length + 1) = bound * xs.length + bound := Nat.mul_succ bound xs.length
    omega

theorem sumOver_le_mul (n : Nat) (f : Nat → Nat) (bound : Nat)
    (h : ∀ i, i < n → f i ≤ bound) : sumOver n f ≤ bound * n := by
  unfold sumOver
  have := foldl_sum_le_bound (List.range n) f bound 0
    (fun x hx => h x (List.mem_range.mp hx))
  rw [List.length_range] at this; omega

private theorem foldl_sum_contains (l : List Nat) (f : Nat → Nat) (init : Nat) (k : Nat)
    (hk : k ∈ l) :
    init + f k ≤ l.foldl (fun acc i => acc + f i) init := by
  induction l generalizing init with
  | nil => exact absurd hk List.not_mem_nil
  | cons x xs ih =>
    simp [List.foldl]
    cases List.mem_cons.mp hk with
    | inl heq =>
      subst heq
      exact foldl_sum_ge_init xs f (init + f k)
    | inr hmem =>
      have := ih (init + f x) hmem; omega

theorem sumOver_ge_single (n : Nat) (f : Nat → Nat) (k : Nat) (hk : k < n) :
    f k ≤ sumOver n f := by
  unfold sumOver
  have := foldl_sum_contains (List.range n) f 0 k (List.mem_range.mpr hk)
  omega

/-! ## Concrete tests -/

theorem maxOver_test : maxOver 5 (fun i => i * 2) = 8 := by native_decide

theorem countOver_test : countOver 10 (fun i => i % 2 == 0) = 5 := by native_decide

theorem sumOver_test : sumOver 4 (fun i => i) = 6 := by native_decide

end SuperHash.Sbox.FinIter
