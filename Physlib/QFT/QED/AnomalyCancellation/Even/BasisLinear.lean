/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QED.AnomalyCancellation.Even.BasisLinear.SymmPlane
public import Physlib.QFT.QED.AnomalyCancellation.Even.BasisLinear.ShiftPlane
/-!

# Splitting the linear solutions in the even case into two ACC-satisfying planes

## i. Overview

We split the linear solutions of `PureU1 (2 * n.succ)` into two planes,
where every point in either plane satisfies both the linear and cubic anomaly cancellation
conditions.

The two planes are named after the charge-index splitting they are built from:
- The **symmetric plane** (`SymmPlane`): basis vectors pair charges at positions from the
  symmetric (even) split `n.succ + n.succ`.
- The **shifted plane** (`ShiftPlane`): basis vectors pair charges at positions from the
  shifted even split `1 + (n + n + 1)`.

## ii. Key results

- `Psymm'` : The inclusion of the symmetric plane into linear solutions.
- `Psymm_accCube` : The statement that charges from the symmetric plane satisfy the cubic ACC.
- `Pshift'` : The inclusion of the shifted plane into linear solutions.
- `Pshift_accCube` : The statement that charges from the shifted plane satisfy the cubic ACC.
- `span_basis` : Every linear solution is the sum of a point from each plane.

## iii. Table of contents

- D. Mixed cubic ACCs involving points from both planes
- E. The combined basis
  - E.1. As a map into linear solutions
  - E.2. Inclusion of the span of the basis into charges
  - E.3. Components of the inclusion into charges
  - E.4. Kernel of the inclusion into charges
  - E.5. The inclusion of the span of the basis into linear solutions
  - E.6. The combined basis vectors are linearly independent
  - E.7. Injectivity of the inclusion into linear solutions
  - E.8. Cardinality of the basis
  - E.9. The basis vectors as a basis
- F. Every linear solution is the sum of a point from each plane
  - F.1. Relation under permutations

## iv. References

- https://arxiv.org/pdf/1912.04804.pdf

-/

@[expose] public section

open Nat Module Finset BigOperators

namespace PureU1

variable {n : ℕ}

namespace VectorLikeEvenPlane

/-!

## D. Mixed cubic ACCs involving points from both planes

-/

set_option backward.isDefEq.respectTransparency false in
lemma Psymm_Psymm_shiftBasis_accCube (g : Fin n.succ → ℚ) (j : Fin n) :
    accCubeTriLinSymm (Psymm g) (Psymm g) (shiftBasisAsCharges j)
    = g (j.succ) ^ 2 - g (j.castSucc) ^ 2 := by
  simp only [succ_eq_add_one, accCubeTriLinSymm, PureU1Charges_numberCharges,
    TriLinearSymm.mk₃_toFun_apply_apply]
  rw [sum_evenShift, shiftBasis_on_evenShiftZero, shiftBasis_on_evenShiftLast]
  simp only [mul_zero, add_zero, Function.comp_apply, zero_add]
  rw [Finset.sum_eq_single j, shiftBasis_on_evenShiftFst_self, shiftBasis_on_evenShiftSnd_self]
  · simp only [evenShiftFst_eq_evenFst_succ, mul_one, evenShiftSnd_eq_evenSnd_castSucc, mul_neg]
    rw [Psymm_evenFst, Psymm_evenSnd]
    ring
  · intro k _ hkj
    erw [shiftBasis_on_evenShiftFst_other hkj.symm, shiftBasis_on_evenShiftSnd_other hkj.symm]
    simp only [mul_zero, add_zero]
  · simp

set_option backward.isDefEq.respectTransparency false in
lemma Psymm_Pshift_Pshift_accCube (g : Fin n → ℚ) (j : Fin n.succ) :
    accCubeTriLinSymm (Pshift g) (Pshift g) (symmBasisAsCharges j)
    = (Pshift g (evenFst j))^2 - (Pshift g (evenSnd j))^2 := by
  simp only [succ_eq_add_one, accCubeTriLinSymm, PureU1Charges_numberCharges,
    TriLinearSymm.mk₃_toFun_apply_apply]
  rw [sum_even]
  simp only [Function.comp_apply]
  rw [Finset.sum_eq_single j, symmBasis_on_evenFst_self, symmBasis_on_evenSnd_self]
  · simp only [mul_one, mul_neg]
    ring
  · intro k _ hkj
    erw [symmBasis_on_evenFst_other hkj.symm, symmBasis_on_evenSnd_other hkj.symm]
    simp only [mul_zero, add_zero]
  · simp

/-!

## E. The combined basis

-/

/-!

### E.1. As a map into linear solutions

-/
/-- The whole basis as `LinSols`. -/
def basisa : (Fin n.succ) ⊕ (Fin n) → (PureU1 (2 * n.succ)).LinSols := fun i =>
  match i with
  | .inl i => symmBasis i
  | .inr i => shiftBasis i

/-!

### E.2. Inclusion of the span of the basis into charges

-/

/-- A point in the span of the basis as a charge. -/
def Pa (f : Fin n.succ → ℚ) (g : Fin n → ℚ) : (PureU1 (2 * n.succ)).Charges := Psymm f + Pshift g

/-!

### E.3. Components of the inclusion into charges

-/

lemma Pa_evenShiftFst (f : Fin n.succ → ℚ) (g : Fin n → ℚ) (j : Fin n) :
    Pa f g (evenShiftFst j) = f j.succ + g j := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  rw [Pshift_evenShiftFst, evenShiftFst_eq_evenFst_succ, Psymm_evenFst]

lemma Pa_evenShiftSnd (f : Fin n.succ → ℚ) (g : Fin n → ℚ) (j : Fin n) :
    Pa f g (evenShiftSnd j) = - f j.castSucc - g j := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  rw [Pshift_evenShiftSnd, evenShiftSnd_eq_evenSnd_castSucc, Psymm_evenSnd]
  ring

lemma Pa_evenShiftZero (f : Fin n.succ → ℚ) (g : Fin n → ℚ) : Pa f g (evenShiftZero) = f 0 := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  rw [Pshift_evenShiftZero, evenShiftZero_eq_evenFst_zero, Psymm_evenFst]
  exact Rat.add_zero (f 0)

lemma Pa_evenShiftLast (f : Fin n.succ → ℚ) (g : Fin n → ℚ) :
    Pa f g (evenShiftLast) = - f (Fin.last n) := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  rw [Pshift_evenShiftLast, evenShiftLast_eq_evenSnd_last, Psymm_evenSnd]
  exact Rat.add_zero (-f (Fin.last n))

/-!

### E.4. Kernel of the inclusion into charges

-/

set_option backward.isDefEq.respectTransparency false in
lemma Pa_zero (f : Fin n.succ → ℚ) (g : Fin n → ℚ) (h : Pa f g = 0) :
    ∀ i, f i = 0 := by
  have h₃ := Pa_evenShiftZero f g
  rw [h] at h₃
  change 0 = f 0 at h₃
  intro i
  have hinduc (iv : ℕ) (hiv : iv < n.succ) : f ⟨iv, hiv⟩ = 0 := by
    induction iv
    exact h₃.symm
    rename_i iv hi
    have hivi : iv < n.succ := lt_of_succ_lt hiv
    have hi2 := hi hivi
    have h1 := Pa_evenShiftFst f g ⟨iv, succ_lt_succ_iff.mp hiv⟩
    have h2 := Pa_evenShiftSnd f g ⟨iv, succ_lt_succ_iff.mp hiv⟩
    rw [h] at h1 h2
    simp only [Fin.succ_mk, Fin.castSucc_mk] at h1 h2
    erw [hi2] at h2
    change 0 = _ at h2
    simp only [neg_zero, zero_sub, zero_eq_neg] at h2
    rw [h2] at h1
    exact right_eq_add.mp h1
  exact hinduc i.val i.prop

lemma Pa_zero_shift (f : Fin n.succ → ℚ) (g : Fin n → ℚ) (h : Pa f g = 0) :
    ∀ i, g i = 0 := by
  have hf := Pa_zero f g h
  rw [Pa, Psymm] at h
  simp only [succ_eq_add_one, hf, zero_smul, sum_const_zero, zero_add] at h
  exact Pshift_zero g h

/-!

### E.5. The inclusion of the span of the basis into linear solutions

-/
/-- A point in the span of the whole basis. -/
def Pa' (f : (Fin n.succ) ⊕ (Fin n) → ℚ) : (PureU1 (2 * n.succ)).LinSols :=
    ∑ i, f i • basisa i

lemma Pa'_Psymm'_Pshift' (f : (Fin n.succ) ⊕ (Fin n) → ℚ) :
    Pa' f = Psymm' (f ∘ Sum.inl) + Pshift' (f ∘ Sum.inr) := by
  exact Fintype.sum_sum_type _

/-!

### E.6. The combined basis vectors are linearly independent

-/

theorem basisa_linear_independent : LinearIndependent ℚ (@basisa n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change Pa' f = 0 at h
  have h1 : (Pa' f).val = 0 :=
    (AddSemiconjBy.eq_zero_iff (ACCSystemLinear.LinSols.val 0)
    (congrFun (congrArg HAdd.hAdd (congrArg ACCSystemLinear.LinSols.val (id (Eq.symm h))))
    (ACCSystemLinear.LinSols.val 0))).mp rfl
  rw [Pa'_Psymm'_Pshift'] at h1
  change (Psymm' (f ∘ Sum.inl)).val + (Pshift' (f ∘ Sum.inr)).val = 0 at h1
  rw [Pshift'_val, Psymm'_val] at h1
  change Pa (f ∘ Sum.inl) (f ∘ Sum.inr) = 0 at h1
  have hf := Pa_zero (f ∘ Sum.inl) (f ∘ Sum.inr) h1
  have hg := Pa_zero_shift (f ∘ Sum.inl) (f ∘ Sum.inr) h1
  intro i
  simp_all
  cases i
  · simp_all
  · simp_all
/-!

### E.7. Injectivity of the inclusion into linear solutions

-/

lemma Pa'_eq (f f' : (Fin n.succ) ⊕ (Fin n) → ℚ) : Pa' f = Pa' f' ↔ f = f' := by
  refine Iff.intro (fun h => (funext (fun i => ?_))) (fun h => ?_)
  · rw [Pa', Pa'] at h
    have h1 : ∑ i : Fin (succ n) ⊕ Fin n, (f i + (- f' i)) • basisa i = 0 := by
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

lemma Pa'_elim_eq_iff (g g' : Fin n.succ → ℚ) (f f' : Fin n → ℚ) :
    Pa' (Sum.elim g f) = Pa' (Sum.elim g' f') ↔ Pa g f = Pa g' f' := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rw [Pa'_eq, Sum.elim_eq_iff] at h
    rw [h.left, h.right]
  · apply ACCSystemLinear.LinSols.ext
    rw [Pa'_Psymm'_Pshift', Pa'_Psymm'_Pshift']
    simp only [succ_eq_add_one, ACCSystemLinear.linSolsAddCommMonoid_add_val, Psymm'_val, Pshift'_val]
    exact h

lemma Pa_eq (g g' : Fin n.succ → ℚ) (f f' : Fin n → ℚ) :
    Pa g f = Pa g' f' ↔ g = g' ∧ f = f' := by
  rw [← Pa'_elim_eq_iff, ← Sum.elim_eq_iff]
  exact Pa'_eq _ _

/-!

### E.8. Cardinality of the basis

-/

lemma basisa_card : Fintype.card ((Fin n.succ) ⊕ (Fin n)) =
    Module.finrank ℚ (PureU1 (2 * n.succ)).LinSols := by
  erw [BasisLinear.finrank_AnomalyFreeLinear]
  simp only [Fintype.card_sum, Fintype.card_fin, mul_eq]
  exact split_odd n

/-!

### E.9. The basis vectors as a basis

-/

/-- The basis formed out of our `basisa` vectors. -/
noncomputable def basisaAsBasis :
    Basis (Fin (succ n) ⊕ Fin n) ℚ (PureU1 (2 * succ n)).LinSols :=
  basisOfLinearIndependentOfCardEqFinrank (@basisa_linear_independent n) basisa_card

/-!

## F. Every linear solution is the sum of a point from each plane

-/

lemma span_basis (S : (PureU1 (2 * n.succ)).LinSols) :
    ∃ (g : Fin n.succ → ℚ) (f : Fin n → ℚ), S.val = Psymm g + Pshift f := by
  have h := (Submodule.mem_span_range_iff_exists_fun ℚ).mp (Basis.mem_span basisaAsBasis S)
  obtain ⟨f, hf⟩ := h
  simp only [succ_eq_add_one, basisaAsBasis, coe_basisOfLinearIndependentOfCardEqFinrank,
    Fintype.sum_sum_type] at hf
  change Psymm' _ + Pshift' _ = S at hf
  use f ∘ Sum.inl
  use f ∘ Sum.inr
  rw [← hf]
  simp only [succ_eq_add_one, ACCSystemLinear.linSolsAddCommMonoid_add_val, Psymm'_val, Pshift'_val]
  rfl

/-!

### F.1. Relation under permutations

-/
lemma span_basis_swapShift {S : (PureU1 (2 * n.succ)).LinSols} (j : Fin n)
    (hS : ((FamilyPermutations (2 * n.succ)).linSolRep
    (Equiv.swap (evenShiftFst j) (evenShiftSnd j))) S = S') (g : Fin n.succ → ℚ) (f : Fin n → ℚ)
    (h : S.val = Psymm g + Pshift f) : ∃ (g' : Fin n.succ → ℚ) (f' : Fin n → ℚ),
      S'.val = Psymm g' + Pshift f' ∧ Pshift f' = Pshift f +
      (S.val (evenShiftSnd j) - S.val (evenShiftFst j)) • shiftBasisAsCharges j ∧ g' = g := by
  let X := Pshift f + (S.val (evenShiftSnd j) - S.val (evenShiftFst j)) • shiftBasisAsCharges j
  have hX : X ∈ Submodule.span ℚ (Set.range (shiftBasisAsCharges)) := by
    apply Submodule.add_mem
    exact (Pshift_in_span f)
    exact (smul_shiftBasisAsCharges_in_span S j)
  have hXsum := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hX
  obtain ⟨f', hf'⟩ := hXsum
  use g
  use f'
  change Pshift f' = _ at hf'
  erw [hf']
  simp only [and_self, and_true, X]
  rw [← add_assoc, ← h]
  apply swapShift_as_add at hS
  exact hS

end VectorLikeEvenPlane

end PureU1
