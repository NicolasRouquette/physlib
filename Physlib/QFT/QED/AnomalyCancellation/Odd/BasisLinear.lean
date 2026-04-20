/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QED.AnomalyCancellation.Odd.BasisLinear.ShiftPlane
/-!
# The combined basis for the odd case

This file combines the symmetric and shifted planes into a single basis for the linear solutions
of `PureU1 (2 * n + 1)`. Every linear solution is the sum of a point from each plane.

## Key results

- `span_basis` : Every linear solution is the sum of a point from each plane.
- `symmPlaneLinSols` : The inclusion of the symmetric plane into linear solutions.
- `shiftPlaneLinSols` : The inclusion of the shifted plane into linear solutions.
- `basisa_linear_independent` : The combined basis vectors are linearly independent.
- `basisaAsBasis` : The combined basis as a `Basis`.

## Table of contents

- E. The combined basis
  - E.1. The combined basis as `LinSols`
  - E.2. The inclusion of the span of the combined basis into charges
  - E.3. Components of the inclusion
  - E.4. Kernel of the inclusion into charges
  - E.5. The inclusion of the span of the combined basis into LinSols
  - E.6. The combined basis vectors are linearly independent
  - E.7. Injectivity of the inclusion into linear solutions
  - E.8. Cardinality of the basis
  - E.9. The basis vectors as a basis
- F. Every linear solution is the sum of a point from each plane
  - F.1. Relation under permutations

-/

@[expose] public section

open Module Nat Finset BigOperators

namespace PureU1

variable {n : ℕ}

namespace VectorLikeOddPlane

/-!

## E. The combined basis

-/

/-!

### E.1. The combined basis as `LinSols`

-/

/-- The whole basis as `LinSols`. -/
def basisa : Fin n ⊕ Fin n → (PureU1 (2 * n + 1)).LinSols := fun i =>
  match i with
  | .inl i => symmBasis i
  | .inr i => shiftBasis i

/-!

### E.2. The inclusion of the span of the combined basis into charges

-/

/-- A point in the span of the basis as a charge. -/
def Pa (f : Fin n → ℚ) (g : Fin n → ℚ) : (PureU1 (2 * n + 1)).Charges :=
  symmPlane f + shiftPlane g

/-!

### E.3. Components of the inclusion

-/

lemma Pa_oddShiftShiftZero (f g : Fin n.succ → ℚ) : Pa f g oddShiftShiftZero = f 0 := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  nth_rewrite 1 [oddShiftShiftZero_eq_oddFst_zero]
  rw [oddShiftShiftZero_eq_oddShiftZero]
  rw [shiftPlane_oddShiftZero, oddShiftZero_eq_oddFst, symmPlane_oddFst]
  exact Rat.add_zero (f 0)

lemma Pa_oddShiftShiftFst (f g : Fin n.succ → ℚ) (j : Fin n) :
    Pa f g (oddShiftShiftFst j) = f j.succ + g j.castSucc := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  nth_rewrite 1 [oddShiftShiftFst_eq_oddFst_succ]
  rw [oddShiftShiftFst_eq_oddShiftFst_castSucc]
  rw [shiftPlane_oddShiftFst, oddShiftFst_castSucc_eq_oddFst_succ, symmPlane_oddFst]

lemma Pa_oddShiftShiftMid (f g : Fin n.succ → ℚ) :
    Pa f g oddShiftShiftMid = g (Fin.last n) := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  nth_rewrite 1 [oddShiftShiftMid_eq_oddMid]
  rw [oddShiftShiftMid_eq_oddShiftFst_last]
  rw [shiftPlane_oddShiftFst, oddShiftFst_last_eq_oddMid, symmPlane_oddMid]
  exact Rat.zero_add (g (Fin.last n))

lemma Pa_oddShiftShiftSnd (f g : Fin n.succ → ℚ) (j : Fin n.succ) :
    Pa f g (oddShiftShiftSnd j) = - f j - g j := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  nth_rewrite 1 [oddShiftShiftSnd_eq_oddSnd]
  rw [oddShiftShiftSnd_eq_oddShiftSnd]
  rw [shiftPlane_oddShiftSnd, oddShiftSnd_eq_oddSnd, symmPlane_oddSnd]
  ring

/-!

### E.4. Kernel of the inclusion into charges

-/

set_option backward.isDefEq.respectTransparency false in
lemma Pa_zero (f g : Fin n.succ → ℚ) (h : Pa f g = 0) :
    ∀ i, f i = 0 := by
  have h₃ := Pa_oddShiftShiftZero f g
  rw [h] at h₃
  change 0 = _ at h₃
  intro i
  have hinduc (iv : ℕ) (hiv : iv < n.succ) : f ⟨iv, hiv⟩ = 0 := by
    induction iv
    exact h₃.symm
    rename_i iv hi
    have hivi : iv < n.succ := lt_of_succ_lt hiv
    have hi2 := hi hivi
    have h1 := Pa_oddShiftShiftSnd f g ⟨iv, hivi⟩
    rw [h, hi2] at h1
    change 0 = _ at h1
    simp only [neg_zero, succ_eq_add_one, zero_sub, zero_eq_neg] at h1
    have h2 := Pa_oddShiftShiftFst f g ⟨iv, succ_lt_succ_iff.mp hiv⟩
    simp only [succ_eq_add_one, h, Fin.succ_mk, Fin.castSucc_mk, h1, add_zero] at h2
    exact h2.symm
  exact hinduc i.val i.prop

lemma Pa_zero_shift (f g : Fin n.succ → ℚ) (h : Pa f g = 0) :
    ∀ i, g i = 0 := by
  have hf := Pa_zero f g h
  rw [Pa, symmPlane] at h
  simp only [succ_eq_add_one, hf, zero_smul, sum_const_zero, zero_add] at h
  exact shiftPlane_zero g h

/-!

### E.5. The inclusion of the span of the combined basis into LinSols

-/

/-- A point in the span of the whole basis. -/
def Pa' (f : (Fin n) ⊕ (Fin n) → ℚ) : (PureU1 (2 * n + 1)).LinSols :=
    ∑ i, f i • basisa i

lemma Pa'_symmPlaneLinSols_shiftPlaneLinSols (f : (Fin n) ⊕ (Fin n) → ℚ) :
    Pa' f = symmPlaneLinSols (f ∘ Sum.inl) + shiftPlaneLinSols (f ∘ Sum.inr) := by
  exact Fintype.sum_sum_type _

/-!

### E.6. The combined basis vectors are linearly independent

-/

theorem basisa_linear_independent : LinearIndependent ℚ (@basisa n.succ) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change Pa' f = 0 at h
  have h1 : (Pa' f).val = 0 :=
    (AddSemiconjBy.eq_zero_iff (ACCSystemLinear.LinSols.val 0)
    (congrFun (congrArg HAdd.hAdd (congrArg ACCSystemLinear.LinSols.val (id (Eq.symm h))))
    (ACCSystemLinear.LinSols.val 0))).mp rfl
  rw [Pa'_symmPlaneLinSols_shiftPlaneLinSols] at h1
  change (symmPlaneLinSols (f ∘ Sum.inl)).val + (shiftPlaneLinSols (f ∘ Sum.inr)).val = 0 at h1
  rw [shiftPlaneLinSols_val, symmPlaneLinSols_val] at h1
  change Pa (f ∘ Sum.inl) (f ∘ Sum.inr) = 0 at h1
  have hf := Pa_zero (f ∘ Sum.inl) (f ∘ Sum.inr) h1
  have hg := Pa_zero_shift (f ∘ Sum.inl) (f ∘ Sum.inr) h1
  intro i
  simp_all only [succ_eq_add_one, Function.comp_apply]
  cases i
  · simp_all
  · simp_all

/-!

### E.7. Injectivity of the inclusion into linear solutions

-/

lemma Pa'_eq (f f' : (Fin n.succ) ⊕ (Fin n.succ) → ℚ) : Pa' f = Pa' f' ↔ f = f' := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · funext i
    rw [Pa', Pa'] at h
    have h1 : ∑ i : Fin n.succ ⊕ Fin n.succ, (f i + (- f' i)) • basisa i = 0 := by
      simp only [add_smul, neg_smul]
      rw [Finset.sum_add_distrib]
      rw [h]
      rw [← Finset.sum_add_distrib]
      simp
    have h2 : ∀ i, (f i + (- f' i)) = 0 := by
      exact Fintype.linearIndependent_iff.mp (@basisa_linear_independent n)
        (fun i => f i + -f' i) h1
    have h2i := h2 i
    linarith
  · rw [h]

lemma Pa'_elim_eq_iff (g g' : Fin n.succ → ℚ) (f f' : Fin n.succ → ℚ) :
    Pa' (Sum.elim g f) = Pa' (Sum.elim g' f') ↔ Pa g f = Pa g' f' := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rw [Pa'_eq, Sum.elim_eq_iff] at h
    rw [h.left, h.right]
  · apply ACCSystemLinear.LinSols.ext
    rw [Pa'_symmPlaneLinSols_shiftPlaneLinSols, Pa'_symmPlaneLinSols_shiftPlaneLinSols]
    simp only [succ_eq_add_one, ACCSystemLinear.linSolsAddCommMonoid_add_val,
      symmPlaneLinSols_val, shiftPlaneLinSols_val]
    exact h

lemma Pa_eq (g g' : Fin n.succ → ℚ) (f f' : Fin n.succ → ℚ) :
    Pa g f = Pa g' f' ↔ g = g' ∧ f = f' := by
  rw [← Pa'_elim_eq_iff]
  rw [← Sum.elim_eq_iff]
  exact Pa'_eq _ _

/-!

### E.8. Cardinality of the basis

-/

lemma basisa_card : Fintype.card ((Fin n.succ) ⊕ (Fin n.succ)) =
    Module.finrank ℚ (PureU1 (2 * n.succ + 1)).LinSols := by
  erw [BasisLinear.finrank_AnomalyFreeLinear]
  simp only [Fintype.card_sum, Fintype.card_fin]
  exact Eq.symm (Nat.two_mul n.succ)

/-!

### E.9. The basis vectors as a basis

-/

/-- The basis formed out of our basisa vectors. -/
noncomputable def basisaAsBasis :
    Basis (Fin n.succ ⊕ Fin n.succ) ℚ (PureU1 (2 * n.succ + 1)).LinSols :=
  basisOfLinearIndependentOfCardEqFinrank (@basisa_linear_independent n) basisa_card

/-!

## F. Every linear solution is the sum of a point from each plane

-/

lemma span_basis (S : (PureU1 (2 * n.succ + 1)).LinSols) :
    ∃ (g f : Fin n.succ → ℚ), S.val = symmPlane g + shiftPlane f := by
  have h := (Submodule.mem_span_range_iff_exists_fun ℚ).mp (Basis.mem_span basisaAsBasis S)
  obtain ⟨f, hf⟩ := h
  simp only [succ_eq_add_one, basisaAsBasis, coe_basisOfLinearIndependentOfCardEqFinrank,
    Fintype.sum_sum_type] at hf
  change symmPlaneLinSols _ + shiftPlaneLinSols _ = S at hf
  use f ∘ Sum.inl
  use f ∘ Sum.inr
  rw [← hf]
  simp only [succ_eq_add_one, ACCSystemLinear.linSolsAddCommMonoid_add_val,
    symmPlaneLinSols_val, shiftPlaneLinSols_val]
  rfl

/-!

### F.1. Relation under permutations

-/

lemma span_basis_swapShift {S : (PureU1 (2 * n.succ + 1)).LinSols} (j : Fin n.succ)
    (hS : ((FamilyPermutations (2 * n.succ + 1)).linSolRep
    (Equiv.swap (oddShiftFst j) (oddShiftSnd j))) S = S') (g f : Fin n.succ → ℚ)
    (hS1 : S.val = symmPlane g + shiftPlane f) : ∃ (g' f' : Fin n.succ → ℚ),
    S'.val = symmPlane g' + shiftPlane f' ∧ shiftPlane f' = shiftPlane f +
    (S.val (oddShiftSnd j) - S.val (oddShiftFst j)) • shiftBasisAsCharges j ∧ g' = g := by
  let X := shiftPlane f +
    (S.val (oddShiftSnd j) - S.val (oddShiftFst j)) • shiftBasisAsCharges j
  have hf : shiftPlane f ∈ Submodule.span ℚ (Set.range shiftBasisAsCharges) := by
    rw [(Submodule.mem_span_range_iff_exists_fun ℚ)]
    use f
    rfl
  have hP : (S.val (oddShiftSnd j) - S.val (oddShiftFst j)) • shiftBasisAsCharges j ∈
      Submodule.span ℚ (Set.range shiftBasisAsCharges) := by
    apply Submodule.smul_mem
    apply SetLike.mem_of_subset
    apply Submodule.subset_span
    simp_all only [Set.mem_range, exists_apply_eq_apply]
  have hX : X ∈ Submodule.span ℚ (Set.range (shiftBasisAsCharges)) := by
    apply Submodule.add_mem
    exact hf
    exact hP
  have hXsum := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hX
  obtain ⟨f', hf'⟩ := hXsum
  use g
  use f'
  change shiftPlane f' = _ at hf'
  erw [hf']
  simp only [and_self, and_true, X]
  rw [← add_assoc, ← hS1]
  apply swapShift_as_add at hS
  exact hS

end VectorLikeOddPlane

end PureU1
