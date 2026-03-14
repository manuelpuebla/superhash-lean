import SuperHash.Concrete.BitVecOps

/-!
# SuperHash.Concrete.Bridge — Abstract-Concrete bridge theorems (N3.2)

NOTE: These bridges connect BitVec↔Nat layers for fallback operations.
Not yet integrated into the main pipeline (which uses evalCryptoSem over
CryptoSemantics). Future work: CryptoSemantics pipeline with BitVec-backed
S-box evaluation via CertifiedSbox.

Proves that for operations handled by fallback (non-bitwise), the
concrete BitVec evaluation matches the abstract Nat evaluation.

## Key Design (D9)
XOR diverges intentionally: abstract uses addition, concrete uses bitwise XOR.
The bridge only covers operations where both layers agree.
-/

namespace SuperHash

/-- Concrete XOR is bounded: output < 2^n. -/
theorem bvXor_bounded (a b : BitVec n) : (bvXor a b).toNat < 2 ^ n :=
  (bvXor a b).isLt

/-- For sbox (fallback), concrete = abstract. -/
theorem sbox_bridge (n : Nat) (d c : Nat) (args : List Nat) (hargs : args = [c]) :
    evalCryptoOpBitVec n (.sbox d 0) args = evalCryptoOp (.sbox d 0) args := by
  subst hargs; simp [evalCryptoOpBitVec, evalCryptoOp]

/-- For iterate (fallback), concrete = abstract. -/
theorem iterate_bridge (n k : Nat) (b : Nat) (args : List Nat) (hargs : args = [b]) :
    evalCryptoOpBitVec n (.iterate k 0) args = evalCryptoOp (.iterate k 0) args := by
  subst hargs; simp [evalCryptoOpBitVec, evalCryptoOp]

/-- For compose (fallback), concrete = abstract. -/
theorem compose_bridge (n : Nat) (args : List Nat) (hargs : args = [a, b]) :
    evalCryptoOpBitVec n (.compose 0 0) args = evalCryptoOp (.compose 0 0) args := by
  subst hargs; simp [evalCryptoOpBitVec, evalCryptoOp]

/-- For spnBlock (fallback), concrete = abstract. -/
theorem spnBlock_bridge (n r : Nat) (args : List Nat) (hargs : args = [s, l]) :
    evalCryptoOpBitVec n (.spnBlock r 0 0) args = evalCryptoOp (.spnBlock r 0 0) args := by
  subst hargs; simp [evalCryptoOpBitVec, evalCryptoOp]

-- Non-vacuity examples
example : evalCryptoOpBitVec 8 (.sbox 7 0) [10] = evalCryptoOp (.sbox 7 0) [10] := by
  simp [evalCryptoOpBitVec, evalCryptoOp]

example : evalCryptoOpBitVec 8 (.iterate 10 0) [8] = evalCryptoOp (.iterate 10 0) [8] := by
  simp [evalCryptoOpBitVec, evalCryptoOp]

end SuperHash
