import SuperHash.Rules.CryptoRules

/-!
# SuperHash.Rules.SubstitutionRules — S-box substitution strategies (v4.5.4)

Extends the rewrite rule infrastructure with strategies for substituting
S-box components in hash designs. Two strategies:
1. `sboxUpgradeStrategy`: upgrade S-box degree (algebraic security)
2. `spnBlockSboxUpgrade`: upgrade S-box in SPN block constructions
-/

namespace SuperHash

/-- Strategy: substitute S-box with higher algebraic degree.
    Replaces `.sbox d child` with `.sbox targetDeg child` when `d < targetDeg`.
    v4.5.4: extends the v3.0 `sboxSubstituteStrategy` with configurable target. -/
def sboxUpgradeStrategy (targetDeg : Nat) : ImprovementStrategy where
  name := s!"sboxUpgrade_{targetDeg}"
  improve := fun
    | .sbox d c => if d < targetDeg then some (.sbox targetDeg c) else none
    | _ => none
  cost_improves := by
    intro op op' h
    cases op <;> simp at h
    · rename_i d c; obtain ⟨_, rfl⟩ := h; simp [CryptoOp.localCost]; omega

/-- Strategy: upgrade S-box child in SPN blocks.
    Replaces `.spnBlock r (.sbox d child) linear` with `.spnBlock r (.sbox targetDeg child) linear`
    when the S-box degree can be improved.
    Modeled as an ImprovementStrategy on the S-box sub-node; the SPN block
    itself is unchanged — the caller applies this to the sbox child e-class. -/
def spnBlockSboxUpgrade (targetDeg : Nat) : ImprovementStrategy where
  name := s!"spnBlockSboxUpgrade_{targetDeg}"
  improve := fun
    | .sbox d c => if d < targetDeg then some (.sbox targetDeg c) else none
    | _ => none
  cost_improves := by
    intro op op' h
    cases op <;> simp at h
    · rename_i d c; obtain ⟨_, rfl⟩ := h; simp [CryptoOp.localCost]; omega

-- Non-vacuity examples

/-- sboxUpgradeStrategy improves degree 3 → 7 (PRESENT → AES-like). -/
example : (sboxUpgradeStrategy 7).improve (.sbox 3 42) = some (.sbox 7 42) := by native_decide

/-- sboxUpgradeStrategy does not change already-high degree. -/
example : (sboxUpgradeStrategy 7).improve (.sbox 7 42) = none := by native_decide

/-- sboxUpgradeStrategy does not affect non-sbox operations. -/
example : (sboxUpgradeStrategy 7).improve (.linear 5 42) = none := by native_decide

/-- spnBlockSboxUpgrade improves S-box sub-node degree 3 → 11. -/
example : (spnBlockSboxUpgrade 11).improve (.sbox 3 42) = some (.sbox 11 42) := by native_decide

/-- spnBlockSboxUpgrade leaves already-sufficient degree alone. -/
example : (spnBlockSboxUpgrade 11).improve (.sbox 11 42) = none := by native_decide

/-- cost_improves is satisfiable for sboxUpgradeStrategy. -/
example : CryptoOp.localCost (.sbox 7 0) ≥ CryptoOp.localCost (.sbox 3 0) :=
  (sboxUpgradeStrategy 7).cost_improves _ _ rfl

/-- cost_improves is satisfiable for spnBlockSboxUpgrade. -/
example : CryptoOp.localCost (.sbox 11 0) ≥ CryptoOp.localCost (.sbox 3 0) :=
  (spnBlockSboxUpgrade 11).cost_improves _ _ rfl

-- Smoke tests
#eval (sboxUpgradeStrategy 7).improve (.sbox 3 42)   -- some (sbox 7 42)
#eval (sboxUpgradeStrategy 7).improve (.sbox 11 42)  -- none (already good)
#eval (sboxUpgradeStrategy 11).name                   -- "sboxUpgrade_11"
#eval (spnBlockSboxUpgrade 7).improve (.sbox 3 10)   -- some (sbox 7 10)
#eval (spnBlockSboxUpgrade 7).improve (.linear 5 10) -- none (not an sbox)

end SuperHash
