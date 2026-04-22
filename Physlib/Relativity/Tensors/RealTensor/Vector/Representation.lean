/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic

/-!

# Representation of real Lorentz vectors

We define the representation of the Lorentz group on real Lorentz vectors.

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

namespace Vector

attribute [-simp] Fintype.sum_sum_type

/-- The representation of the Lorentz group on `Vector d`. -/
def rep {d : ℕ} : Representation ℝ (LorentzGroup d) (Vector d) where
  toFun Λ := Matrix.toLinAlgEquiv basis Λ
  map_one' := EmbeddingLike.map_eq_one_iff.mpr rfl
  map_mul' x y := by simp only [lorentzGroupIsGroup_mul_coe, _root_.map_mul]

/-!

## Basic equalities

-/

lemma rep_eq_toLinAlgEquiv {d : ℕ} (Λ : LorentzGroup d) (v : Vector d) :
    rep Λ v = Matrix.toLinAlgEquiv basis Λ v := rfl

lemma rep_eq_mulVec {d : ℕ} (Λ : LorentzGroup d) (v : Vector d) :
    rep Λ v = ↑Λ *ᵥ v := by
  funext i
  simp [Matrix.toLinAlgEquiv_apply, apply_sum, apply_smul, rep_eq_toLinAlgEquiv]
  rfl

lemma rep_apply_eq_sum {d : ℕ} (Λ : LorentzGroup d) (v : Vector d) (i : Fin 1 ⊕ Fin d) :
    rep Λ v i = ∑ j, Λ.1 i j * v j := rfl

lemma rep_basis_apply_eq {d : ℕ} (Λ : LorentzGroup d) (i j : Fin 1 ⊕ Fin d) :
    rep Λ (basis i) j = Λ.1 j i := by
  simp [rep_apply_eq_sum]

lemma rep_basis_eq {d : ℕ} (Λ : LorentzGroup d) (i : Fin 1 ⊕ Fin d) :
    rep Λ (basis i) = ∑ j, Λ.1 j i • basis j := by
  funext j
  simp  [rep_basis_apply_eq, apply_sum, basis_apply]

/-!

## Representation is faithful

-/

lemma rep_injective {d : ℕ} : Function.Injective (rep (d := d)) := by
  intro Λ1 Λ2 h
  ext i j
  simp [← rep_basis_apply_eq, h]

end Vector

end Lorentz
