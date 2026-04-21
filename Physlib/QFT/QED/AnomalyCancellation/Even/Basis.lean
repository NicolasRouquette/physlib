/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QED.AnomalyCancellation.Even.BasisLinear.ShiftPlane
/-!

# The combined basis of the symmetric and shifted planes

## i. Overview

This module constructs the combined basis for the linear solutions of
`PureU1 (2 * n.succ)` by combining the two ACC-satisfying planes:

- The *symmetric plane*, named after the symmetric (even) split `n.succ + n.succ`.
  Its key results are `symmPlane` (the inclusion into linear solutions) and
  `symmPlaneAsCharges_accCube` (every point satisfies the cubic anomaly cancellation condition).

- The *shifted plane*, named after the shifted split `1 + (n + n + 1)`.
  Its key results are `shiftPlane` (the inclusion into linear solutions) and
  `shiftPlaneAsCharges_accCube` (every point satisfies the cubic anomaly cancellation condition).

The main result is `span_basis`: every linear solution of `PureU1 (2 * n.succ)` can
be written as the sum of a point from the symmetric plane and a point from the shifted
plane.

## ii. Key results

- `basis` : The combined basis vectors from both planes
- `basis_linear_independent` : The combined basis vectors are linearly independent
- `basisAsBasis` : The combined basis vectors form a basis
- `span_basis` : Every linear solution is the sum of a point from each plane

## iii. Table of contents

- 1. The combined basis
  - 1.1. As a map into linear solutions
  - 1.2. Inclusion of the span of the basis into charges
  - 1.3. Components of the inclusion into charges
  - 1.4. Kernel of the inclusion into charges
  - 1.5. The inclusion of the span of the basis into linear solutions
  - 1.6. The combined basis vectors are linearly independent
  - 1.7. Injectivity of the inclusion into linear solutions
  - 1.8. Cardinality of the basis
  - 1.9. The basis vectors as a basis
- 2. Every linear solution is the sum of a point from each plane
  - 2.1. Relation under permutations

## iv. References

- https://arxiv.org/pdf/1912.04804.pdf

-/

@[expose] public section

open Nat Module Finset BigOperators

namespace PureU1

variable {n : ℕ}

namespace VectorLikeEvenPlane

/-!

## 1. The combined basis

-/

/-!

### 1.1. As a map into linear solutions

-/
/-- The whole basis as `LinSols`. -/
def basis : (Fin n.succ) ⊕ (Fin n) → (PureU1 (2 * n.succ)).LinSols := fun i =>
  match i with
  | .inl i => symmBasis i
  | .inr i => shiftBasis i

/-!

### 1.2. Inclusion of the span of the basis into charges

-/

/-- A point in the span of the basis as a charge. -/
def basisCharge (f : Fin n.succ → ℚ) (g : Fin n → ℚ) : (PureU1 (2 * n.succ)).Charges :=
  symmPlaneAsCharges f + shiftPlaneAsCharges g

/-!

### 1.3. Components of the inclusion into charges

-/

lemma basisCharge_evenShiftFst (f : Fin n.succ → ℚ) (g : Fin n → ℚ) (j : Fin n) :
    basisCharge f g (evenShiftFst j) = f j.succ + g j := by
  rw [basisCharge]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  rw [shiftPlaneAsCharges_evenShiftFst, evenShiftFst_eq_evenFst_succ, symmPlaneAsCharges_evenFst]

lemma basisCharge_evenShiftSnd (f : Fin n.succ → ℚ) (g : Fin n → ℚ) (j : Fin n) :
    basisCharge f g (evenShiftSnd j) = - f j.castSucc - g j := by
  rw [basisCharge]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  rw [shiftPlaneAsCharges_evenShiftSnd, evenShiftSnd_eq_evenSnd_castSucc, symmPlaneAsCharges_evenSnd]
  ring

lemma basisCharge_evenShiftZero (f : Fin n.succ → ℚ) (g : Fin n → ℚ) :
    basisCharge f g (evenShiftZero) = f 0 := by
  rw [basisCharge]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  rw [shiftPlaneAsCharges_evenShiftZero, evenShiftZero_eq_evenFst_zero, symmPlaneAsCharges_evenFst]
  exact Rat.add_zero (f 0)

lemma basisCharge_evenShiftLast (f : Fin n.succ → ℚ) (g : Fin n → ℚ) :
    basisCharge f g (evenShiftLast) = - f (Fin.last n) := by
  rw [basisCharge]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  rw [shiftPlaneAsCharges_evenShiftLast, evenShiftLast_eq_evenSnd_last, symmPlaneAsCharges_evenSnd]
  exact Rat.add_zero (-f (Fin.last n))

/-!

### 1.4. Kernel of the inclusion into charges

-/

set_option backward.isDefEq.respectTransparency false in
lemma basisCharge_zero (f : Fin n.succ → ℚ) (g : Fin n → ℚ) (h : basisCharge f g = 0) :
    ∀ i, f i = 0 := by
  have h₃ := basisCharge_evenShiftZero f g
  rw [h] at h₃
  change 0 = f 0 at h₃
  intro i
  have hinduc (iv : ℕ) (hiv : iv < n.succ) : f ⟨iv, hiv⟩ = 0 := by
    induction iv
    exact h₃.symm
    rename_i iv hi
    have hivi : iv < n.succ := lt_of_succ_lt hiv
    have hi2 := hi hivi
    have h1 := basisCharge_evenShiftFst f g ⟨iv, succ_lt_succ_iff.mp hiv⟩
    have h2 := basisCharge_evenShiftSnd f g ⟨iv, succ_lt_succ_iff.mp hiv⟩
    rw [h] at h1 h2
    simp only [Fin.succ_mk, Fin.castSucc_mk] at h1 h2
    erw [hi2] at h2
    change 0 = _ at h2
    simp only [neg_zero, zero_sub, zero_eq_neg] at h2
    rw [h2] at h1
    exact right_eq_add.mp h1
  exact hinduc i.val i.prop

lemma basisCharge_zero_shift (f : Fin n.succ → ℚ) (g : Fin n → ℚ) (h : basisCharge f g = 0) :
    ∀ i, g i = 0 := by
  have hf := basisCharge_zero f g h
  rw [basisCharge, symmPlaneAsCharges] at h
  simp only [succ_eq_add_one, hf, zero_smul, sum_const_zero, zero_add] at h
  exact shiftPlaneAsCharges_zero g h

/-!

### 1.5. The inclusion of the span of the basis into linear solutions

-/
/-- A point in the span of the whole basis. -/
def basisLinSol (f : (Fin n.succ) ⊕ (Fin n) → ℚ) : (PureU1 (2 * n.succ)).LinSols :=
    ∑ i, f i • basis i

lemma basisLinSol_symmPlane_shiftPlane (f : (Fin n.succ) ⊕ (Fin n) → ℚ) :
    basisLinSol f = symmPlane (f ∘ Sum.inl) + shiftPlane (f ∘ Sum.inr) := by
  exact Fintype.sum_sum_type _

/-!

### 1.6. The combined basis vectors are linearly independent

-/

theorem basis_linear_independent : LinearIndependent ℚ (@basis n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change basisLinSol f = 0 at h
  have h1 : (basisLinSol f).val = 0 :=
    (AddSemiconjBy.eq_zero_iff (ACCSystemLinear.LinSols.val 0)
    (congrFun (congrArg HAdd.hAdd (congrArg ACCSystemLinear.LinSols.val (id (Eq.symm h))))
    (ACCSystemLinear.LinSols.val 0))).mp rfl
  rw [basisLinSol_symmPlane_shiftPlane] at h1
  change (symmPlane (f ∘ Sum.inl)).val +
    (shiftPlane (f ∘ Sum.inr)).val = 0 at h1
  rw [shiftPlane_val, symmPlane_val] at h1
  change basisCharge (f ∘ Sum.inl) (f ∘ Sum.inr) = 0 at h1
  have hf := basisCharge_zero (f ∘ Sum.inl) (f ∘ Sum.inr) h1
  have hg := basisCharge_zero_shift (f ∘ Sum.inl) (f ∘ Sum.inr) h1
  intro i
  simp_all
  cases i
  · simp_all
  · simp_all
/-!

### 1.7. Injectivity of the inclusion into linear solutions

-/

lemma basisLinSol_eq (f f' : (Fin n.succ) ⊕ (Fin n) → ℚ) : basisLinSol f = basisLinSol f' ↔ f = f' := by
  refine Iff.intro (fun h => (funext (fun i => ?_))) (fun h => ?_)
  · rw [basisLinSol, basisLinSol] at h
    have h1 : ∑ i : Fin (succ n) ⊕ Fin n, (f i + (- f' i)) • basis i = 0 := by
      simp only [add_smul, neg_smul]
      rw [Finset.sum_add_distrib]
      rw [h]
      rw [← Finset.sum_add_distrib]
      simp
    have h2 : ∀ i, (f i + (- f' i)) = 0 := by
      exact Fintype.linearIndependent_iff.mp (@basis_linear_independent n)
        (fun i => f i + -f' i) h1
    have h2i := h2 i
    linarith
  · rw [h]

lemma basisLinSol_elim_eq_iff (g g' : Fin n.succ → ℚ) (f f' : Fin n → ℚ) :
    basisLinSol (Sum.elim g f) = basisLinSol (Sum.elim g' f') ↔ basisCharge g f = basisCharge g' f' := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rw [basisLinSol_eq, Sum.elim_eq_iff] at h
    rw [h.left, h.right]
  · apply ACCSystemLinear.LinSols.ext
    rw [basisLinSol_symmPlane_shiftPlane, basisLinSol_symmPlane_shiftPlane]
    simp only [succ_eq_add_one, ACCSystemLinear.linSolsAddCommMonoid_add_val,
      symmPlane_val, shiftPlane_val]
    exact h

lemma basisCharge_eq (g g' : Fin n.succ → ℚ) (f f' : Fin n → ℚ) :
    basisCharge g f = basisCharge g' f' ↔ g = g' ∧ f = f' := by
  rw [← basisLinSol_elim_eq_iff, ← Sum.elim_eq_iff]
  exact basisLinSol_eq _ _

/-!

### 1.8. Cardinality of the basis

-/

lemma basis_card : Fintype.card ((Fin n.succ) ⊕ (Fin n)) =
    Module.finrank ℚ (PureU1 (2 * n.succ)).LinSols := by
  erw [BasisLinear.finrank_AnomalyFreeLinear]
  simp only [Fintype.card_sum, Fintype.card_fin, mul_eq]
  exact split_odd n

/-!

### 1.9. The basis vectors as a basis

-/

/-- The basis formed out of our `basis` vectors. -/
noncomputable def basisAsBasis :
    Basis (Fin (succ n) ⊕ Fin n) ℚ (PureU1 (2 * succ n)).LinSols :=
  basisOfLinearIndependentOfCardEqFinrank (@basis_linear_independent n) basis_card

/-!

## 2. Every linear solution is the sum of a point from each plane

-/

lemma span_basis (S : (PureU1 (2 * n.succ)).LinSols) :
    ∃ (g : Fin n.succ → ℚ) (f : Fin n → ℚ), S.val = symmPlaneAsCharges g + shiftPlaneAsCharges f := by
  have h := (Submodule.mem_span_range_iff_exists_fun ℚ).mp (Basis.mem_span basisAsBasis S)
  obtain ⟨f, hf⟩ := h
  simp only [succ_eq_add_one, basisAsBasis, coe_basisOfLinearIndependentOfCardEqFinrank,
    Fintype.sum_sum_type] at hf
  change symmPlane _ + shiftPlane _ = S at hf
  use f ∘ Sum.inl
  use f ∘ Sum.inr
  rw [← hf]
  simp only [succ_eq_add_one, ACCSystemLinear.linSolsAddCommMonoid_add_val,
    symmPlane_val, shiftPlane_val]
  rfl

/-!

### 2.1. Relation under permutations

-/
lemma span_basis_swapShift {S : (PureU1 (2 * n.succ)).LinSols} (j : Fin n)
    (hS : ((FamilyPermutations (2 * n.succ)).linSolRep
    (Equiv.swap (evenShiftFst j) (evenShiftSnd j))) S = S') (g : Fin n.succ → ℚ) (f : Fin n → ℚ)
    (h : S.val = symmPlaneAsCharges g + shiftPlaneAsCharges f) : ∃ (g' : Fin n.succ → ℚ) (f' : Fin n → ℚ),
      S'.val = symmPlaneAsCharges g' + shiftPlaneAsCharges f' ∧ shiftPlaneAsCharges f' = shiftPlaneAsCharges f +
      (S.val (evenShiftSnd j) - S.val (evenShiftFst j)) • shiftBasisAsCharges j ∧ g' = g := by
  let X := shiftPlaneAsCharges f +
    (S.val (evenShiftSnd j) - S.val (evenShiftFst j)) • shiftBasisAsCharges j
  have hX : X ∈ Submodule.span ℚ (Set.range (shiftBasisAsCharges)) := by
    apply Submodule.add_mem
    exact (shiftPlaneAsCharges_in_span f)
    exact (smul_shiftBasisAsCharges_in_span S j)
  have hXsum := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hX
  obtain ⟨f', hf'⟩ := hXsum
  use g
  use f'
  change shiftPlaneAsCharges f' = _ at hf'
  erw [hf']
  simp only [and_self, and_true, X]
  rw [← add_assoc, ← h]
  apply linSolRep_swap_evenShift_eq_add at hS
  exact hS

end VectorLikeEvenPlane

end PureU1
