/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.CoVector.Basic
public import Mathlib.RepresentationTheory.Intertwining

/-!

# Representation of real Lorentz covectors

We define the representation of the Lorentz group on real Lorentz covectors.

This should not be used directly, instead the MulAction of the Lorentz group should be used.

-/

@[expose] public section
open Module IndexNotation
open Matrix
open MatrixGroups
open CategoryTheory
noncomputable section

namespace Lorentz
open realLorentzTensor

namespace CoVector

attribute [-simp] Fintype.sum_sum_type

/-- The representation of the Lorentz group on `CoVector d`. -/
def rep {d : ℕ} : Representation ℝ (LorentzGroup d) (CoVector d) where
  toFun Λ := Matrix.toLinAlgEquiv basis (LorentzGroup.transpose Λ⁻¹)
  map_one' := by
    simp only [inv_one, LorentzGroup.transpose_one, lorentzGroupIsGroup_one_coe, _root_.map_one]
  map_mul' x y := by
    simp only [_root_.mul_inv_rev, LorentzGroup.inv_eq_dual, LorentzGroup.transpose_mul,
      lorentzGroupIsGroup_mul_coe, _root_.map_mul]

/-!

## Basic equalities

-/

lemma rep_eq_toLinAlgEquiv {d : ℕ} (Λ : LorentzGroup d) (v : CoVector d) :
    rep Λ v = Matrix.toLinAlgEquiv basis (LorentzGroup.transpose Λ⁻¹) v := rfl

lemma rep_eq_mulVec {d : ℕ} (Λ : LorentzGroup d) (v :  CoVector d) :
    rep Λ v = ↑Λ⁻¹ᵀ *ᵥ v := by
  funext i
  simp only [rep_eq_toLinAlgEquiv, LorentzGroup.transpose, LorentzGroup.coe_inv,
    toLinAlgEquiv_apply, apply_sum, apply_smul, basis_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rfl

lemma rep_apply_eq_sum {d : ℕ} (Λ : LorentzGroup d) (v : CoVector d) (i : Fin 1 ⊕ Fin d) :
    rep Λ v i = ∑ j, Λ.1⁻¹ᵀ i j * v j := by
  rw [rep_eq_mulVec]
  rfl

lemma rep_basis_apply_eq {d : ℕ} (Λ : LorentzGroup d) (i j : Fin 1 ⊕ Fin d) :
    rep Λ (basis i) j = Λ.1⁻¹ᵀ j i := by
  simp [rep_apply_eq_sum]

lemma rep_basis_eq {d : ℕ} (Λ : LorentzGroup d) (i : Fin 1 ⊕ Fin d) :
    rep Λ (basis i) = ∑ j, Λ.1⁻¹ᵀ j i • basis j := by
  funext j
  simp  [rep_basis_apply_eq, apply_sum, basis_apply]

lemma rep_basis_eq' {d : ℕ} (Λ : LorentzGroup d) (i : Fin 1 ⊕ Fin d) :
    rep Λ (basis i) = ∑ j, (LorentzGroup.transpose Λ⁻¹).1 j i • basis j := by
  simp [rep_basis_eq, LorentzGroup.transpose, LorentzGroup.coe_inv]

/-!

## Representation is faithful

-/

lemma rep_injective {d : ℕ} : Function.Injective (rep (d := d)) := by
  intro Λ1 Λ2 h
  ext1
  suffices h1 : (Λ1.1⁻¹ᵀ : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) = Λ2.1⁻¹ᵀ by
    simp at h1
    simpa using congrArg (fun M => M⁻¹) h1
  ext i j
  rw [← rep_basis_apply_eq, ← rep_basis_apply_eq, h]

end CoVector

end Lorentz
