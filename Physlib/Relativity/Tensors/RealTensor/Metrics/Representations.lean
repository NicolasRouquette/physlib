/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.CoVector.Representation
public import Physlib.Relativity.Tensors.RealTensor.Vector.Representation

/-!

# Metrics as intertwining maps on the representation of real Lorentz vectors and covectors

We define the metric as an intertwining map on the representation of
real Lorentz vectors and covectors.

-/

@[expose] public section
open Module IndexNotation
open Matrix
open MatrixGroups
open CategoryTheory
noncomputable section

namespace Lorentz
open realLorentzTensor
attribute [-simp] Fintype.sum_sum_type


/-!

## Vectors: The metric as an intertwining map on the representation.

-/

namespace Vector

open Representation TensorProduct minkowskiMatrix

/-- The IntertwiningMap corresponding to the metric `η^{μ ν}`. -/
def metric {d : ℕ} : IntertwiningMap (trivial ℝ (LorentzGroup d) ℝ)
    ((rep (d := d)).tprod (rep (d := d))) where
  toFun k := k • ∑ μ, ∑ ν, η μ ν • basis μ ⊗ₜ basis ν
  map_add' k1 k2 := by simp [add_smul]
  map_smul' r k := by simp [smul_smul]
  isIntertwining' Λ := by
    ext
    simp only [Finset.smul_sum, smul_smul, isTrivial_def, LinearMap.comp_id, LinearMap.coe_mk,
      AddHom.coe_mk, one_mul, Representation.tprod_apply, LinearMap.coe_comp, Function.comp_apply,
      map_sum, map_smul, map_tmul, rep_basis_eq, tmul_sum, tmul_smul, sum_tmul, smul_tmul]
    conv_rhs => enter [2, μ]; rw [Finset.sum_comm]; enter [2, ν]; rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]; enter [2, μ]; rw [Finset.sum_comm];
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun μ _ => (Finset.sum_congr rfl (fun ν _ => ?_)))
    simp [← Finset.sum_smul]
    congr
    rw [(LorentzGroup.mem_iff_forall_components_eq_sum Λᵀ).mp
      (LorentzGroup.mem_iff_transpose.mp Λ.2), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun κ _ => (Finset.sum_congr rfl (fun ω _ => ?_)))
    simp only [transpose_apply]
    ring

lemma metric_apply_eq {d : ℕ} (k : ℝ) :
    metric (d := d) k = k • ∑ μ, ∑ ν, η μ ν • basis μ ⊗ₜ basis ν := rfl

lemma metric_invariant_rep {d : ℕ} (Λ : LorentzGroup d) (k : ℝ) :
    (rep (d := d)).tprod (rep (d := d)) Λ (metric k) = metric k := by
  rw [← metric.isIntertwining]
  simp

end Vector

/-!

## CoVectors: The metric as an intertwining map on the representation.

-/

namespace CoVector

open Representation TensorProduct minkowskiMatrix

/-- The IntertwiningMap corresponding to the metric `η_{μ ν}`. -/
def metric {d : ℕ} : IntertwiningMap (trivial ℝ (LorentzGroup d) ℝ)
    ((rep (d := d)).tprod (rep (d := d))) where
  toFun k := k • ∑ μ, ∑ ν, η μ ν • basis μ ⊗ₜ basis ν
  map_add' k1 k2 := by simp [add_smul]
  map_smul' r k := by simp [smul_smul]
  isIntertwining' Λ := by
    ext
    simp only [Finset.smul_sum, smul_smul, isTrivial_def, LinearMap.comp_id, LinearMap.coe_mk,
      AddHom.coe_mk, one_mul, Representation.tprod_apply, LinearMap.coe_comp, Function.comp_apply,
      map_sum, map_smul, map_tmul, rep_basis_eq', tmul_sum, tmul_smul, sum_tmul, smul_tmul]
    conv_rhs => enter [2, μ]; rw [Finset.sum_comm]; enter [2, ν]; rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]; enter [2, μ]; rw [Finset.sum_comm];
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun μ _ => (Finset.sum_congr rfl (fun ν _ => ?_)))
    simp [← Finset.sum_smul]
    generalize (LorentzGroup.transpose Λ⁻¹) = Λ
    congr
    rw [(LorentzGroup.mem_iff_forall_components_eq_sum Λᵀ).mp
      (LorentzGroup.mem_iff_transpose.mp Λ.2), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun κ _ => (Finset.sum_congr rfl (fun ω _ => ?_)))
    simp only [transpose_apply]
    ring

lemma metric_apply_eq {d : ℕ} (k : ℝ) :
    metric (d := d) k = k • ∑ μ, ∑ ν, η μ ν • basis μ ⊗ₜ basis ν := rfl

lemma metric_invariant_rep {d : ℕ} (Λ : LorentzGroup d) (k : ℝ) :
    (rep (d := d)).tprod (rep (d := d)) Λ (metric k) = metric k := by
  rw [← metric.isIntertwining]
  simp

end CoVector

end Lorentz
