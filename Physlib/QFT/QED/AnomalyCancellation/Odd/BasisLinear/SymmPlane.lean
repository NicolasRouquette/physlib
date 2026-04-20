/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QED.AnomalyCancellation.Odd.BasisLinear.ChargeSplits
/-!
# The symmetric plane for the odd case basis

The symmetric plane is the span of basis vectors `symmBasis`, each of which has charge `+1` at
position `oddFst j` and charge `-1` at position `oddSnd j`. It is called "symmetric" because
these positions come from the **symmetric split** of the `2 * n + 1` charge indices into
`(n + 1) + n` (see `ChargeSplits`).

## Key results

- `symmBasisAsCharges` : The basis vectors as charge assignments.
- `symmBasis` : The basis vectors as `LinSols`.
- `Psymm` : The inclusion of the symmetric plane into charges.
- `Psymm_accCube` : Charges from the symmetric plane satisfy the cubic ACC.
- `Psymm'` : The inclusion of the symmetric plane into linear solutions.
-/

@[expose] public section

open Module Nat Finset BigOperators

namespace PureU1

variable {n : ℕ}

namespace VectorLikeOddPlane

/-!

## B. The symmetric plane

-/

/-!

### B.1. The basis vectors of the symmetric plane as charges

-/

/-- The basis vectors of the symmetric plane as charge assignments. -/
def symmBasisAsCharges (j : Fin n) : (PureU1 (2 * n + 1)).Charges :=
  fun i =>
  if i = oddFst j then
    1
  else
    if i = oddSnd j then
      - 1
    else
      0

/-!

### B.2. Components of the basis vectors as charges

-/

lemma symmBasis_on_oddFst_self (j : Fin n) : symmBasisAsCharges j (oddFst j) = 1 := by
  simp [symmBasisAsCharges]

lemma symmBasis_on_oddFst_other {k j : Fin n} (h : k ≠ j) :
    symmBasisAsCharges k (oddFst j) = 0 := by
  simp only [symmBasisAsCharges, PureU1_numberCharges]
  simp only [oddFst, oddSnd]
  split
  · rename_i h1
    rw [Fin.ext_iff] at h1
    simp_all
    rw [Fin.ext_iff] at h
    simp_all
  · split
    · rename_i h1 h2
      simp_all
      rw [Fin.ext_iff] at h2
      simp only [Fin.val_castAdd, Fin.val_natAdd] at h2
      omega
    · rfl

lemma symmBasis_on_other {k : Fin n} {j : Fin (2 * n + 1)} (h1 : j ≠ oddFst k)
    (h2 : j ≠ oddSnd k) :
    symmBasisAsCharges k j = 0 := by
  simp only [symmBasisAsCharges, PureU1_numberCharges]
  simp_all only [ne_eq, ↓reduceIte]

lemma symmBasis_oddSnd_eq_minus_oddFst (j i : Fin n) :
    symmBasisAsCharges j (oddSnd i) = - symmBasisAsCharges j (oddFst i) := by
  simp only [symmBasisAsCharges, PureU1_numberCharges, oddSnd, oddFst]
  split <;> split
  any_goals split
  any_goals split
  any_goals rfl
  all_goals
    rename_i h1 h2
    rw [Fin.ext_iff] at h1 h2
    simp_all only [Fin.cast_inj, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, neg_neg,
      add_eq_right, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true]
  all_goals
    rename_i h3
    rw [Fin.ext_iff] at h3
    simp_all only [Fin.val_natAdd, Fin.val_castAdd, add_eq_right,
      AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true]
  all_goals
    omega

lemma symmBasis_on_oddSnd_self (j : Fin n) : symmBasisAsCharges j (oddSnd j) = - 1 := by
  rw [symmBasis_oddSnd_eq_minus_oddFst, symmBasis_on_oddFst_self]

lemma symmBasis_on_oddSnd_other {k j : Fin n} (h : k ≠ j) :
    symmBasisAsCharges k (oddSnd j) = 0 := by
  rw [symmBasis_oddSnd_eq_minus_oddFst, symmBasis_on_oddFst_other h]
  rfl

lemma symmBasis_on_oddMid (j : Fin n) : symmBasisAsCharges j oddMid = 0 := by
  simp only [symmBasisAsCharges, PureU1_numberCharges]
  split <;> rename_i h
  · rw [Fin.ext_iff] at h
    simp only [oddMid, Fin.isValue, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, Fin.val_eq_zero,
      add_zero, oddFst] at h
    omega
  · split <;> rename_i h2
    · rw [Fin.ext_iff] at h2
      simp only [oddMid, Fin.isValue, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd,
        Fin.val_eq_zero, add_zero, oddSnd] at h2
      omega
    · rfl

/-!

### B.3. The basis vectors satisfy the linear ACCs

-/

lemma symmBasis_linearACC (j : Fin n) :
    (accGrav (2 * n + 1)) (symmBasisAsCharges j) = 0 := by
  rw [accGrav]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  erw [sum_odd]
  simp [symmBasis_oddSnd_eq_minus_oddFst, symmBasis_on_oddMid]

/-!

### B.4. The basis vectors as `LinSols`

-/

/-- The basis vectors of the symmetric plane as `LinSols`. -/
@[simps!]
def symmBasis (j : Fin n) : (PureU1 (2 * n + 1)).LinSols :=
  ⟨symmBasisAsCharges j, by
    intro i
    simp only [PureU1_numberLinear] at i
    match i with
    | 0 =>
    exact symmBasis_linearACC j⟩

/-!

### B.5. The inclusion of the symmetric plane into charges

-/

/-- A point in the span of the symmetric plane basis as a charge. -/
def Psymm (f : Fin n → ℚ) : (PureU1 (2 * n + 1)).Charges := ∑ i, f i • symmBasisAsCharges i

/-!

### B.6. Components of the symmetric plane

-/

lemma Psymm_oddFst (f : Fin n → ℚ) (j : Fin n) : Psymm f (oddFst j) = f j := by
  rw [Psymm, sum_of_charges]
  simp only [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  · rw [symmBasis_on_oddFst_self]
    exact Rat.mul_one (f j)
  · intro k _ hkj
    rw [symmBasis_on_oddFst_other hkj]
    exact Rat.mul_zero (f k)
  · simp only [mem_univ, not_true_eq_false, _root_.mul_eq_zero, IsEmpty.forall_iff]

lemma Psymm_oddSnd (f : Fin n → ℚ) (j : Fin n) : Psymm f (oddSnd j) = - f j := by
  rw [Psymm, sum_of_charges]
  simp only [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  · rw [symmBasis_on_oddSnd_self]
    exact mul_neg_one (f j)
  · intro k _ hkj
    rw [symmBasis_on_oddSnd_other hkj]
    exact Rat.mul_zero (f k)
  · simp

lemma Psymm_oddMid (f : Fin n → ℚ) : Psymm f oddMid = 0 := by
  rw [Psymm, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul, symmBasis_on_oddMid]

/-!

### B.7. Points on the symmetric plane satisfy the ACCs

-/

lemma Psymm_linearACC (f : Fin n → ℚ) : (accGrav (2 * n + 1)) (Psymm f) = 0 := by
  rw [accGrav]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_odd]
  simp [Psymm_oddSnd, Psymm_oddFst, Psymm_oddMid]

set_option backward.isDefEq.respectTransparency false in
lemma Psymm_accCube (f : Fin n → ℚ) : accCube (2 * n +1) (Psymm f) = 0 := by
  rw [accCube_explicit, sum_odd, Psymm_oddMid]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Function.comp_apply,
    zero_add]
  apply Finset.sum_eq_zero
  intro i _
  simp only [Psymm_oddFst, Psymm_oddSnd]
  ring

/-!

### B.8. Kernel of the inclusion into charges

-/

lemma Psymm_zero (f : Fin n → ℚ) (h : Psymm f = 0) : ∀ i, f i = 0 := by
  intro i
  erw [← Psymm_oddFst f]
  rw [h]
  rfl

/-- A point in the span of the symmetric plane basis. -/
def Psymm' (f : Fin n → ℚ) : (PureU1 (2 * n + 1)).LinSols := ∑ i, f i • symmBasis i

lemma Psymm'_val (f : Fin n → ℚ) : (Psymm' f).val = Psymm f := by
  simp only [Psymm', Psymm]
  funext i
  rw [sum_of_anomaly_free_linear, sum_of_charges]
  rfl

/-!

### B.9. The basis vectors are linearly independent

-/

theorem symmBasis_linear_independent : LinearIndependent ℚ (@symmBasis n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change Psymm' f = 0 at h
  have h1 : (Psymm' f).val = 0 :=
    (AddSemiconjBy.eq_zero_iff (ACCSystemLinear.LinSols.val 0)
    (congrFun (congrArg HAdd.hAdd (congrArg ACCSystemLinear.LinSols.val (id (Eq.symm h))))
    (ACCSystemLinear.LinSols.val 0))).mp rfl
  rw [Psymm'_val] at h1
  exact Psymm_zero f h1

end VectorLikeOddPlane

end PureU1
