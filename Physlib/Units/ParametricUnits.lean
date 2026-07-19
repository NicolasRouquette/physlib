/-
Copyright (c) 2026 Nicolas Rouquette. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
module

public import Physlib.Units.Basic
/-!

# The unit side, parametrised in the same basis

The dimension basis is parametric (`Dimension B`), but the *unit* side of the
bridge is hardwired in parallel: `UnitChoices` has five named unit fields and
`UnitChoices.dimScale` folds over exactly those five. This module provides the
generic twin, parametrised in the same basis `B`.

Every PhysLib base unit (`LengthUnit`, `TimeUnit`, …) is, structurally, a positive
real (`{ val : ℝ // 0 < val }`); the typed names carry no extra algebraic content.
So a unit choice over a basis `B` is a positive real per base dimension, and the
scaling homomorphism folds the per-base unit ratio over `B`:

* `UnitScale B` — a positive-real magnitude for each `b : B`.
* `UnitScale.dimScale : UnitScale B → UnitScale B → Dimension B →* ℝ≥0` — the
  `MonoidHom` `d ↦ ∏ b, (u₁ b / u₂ b) ^ d.exponent b`, generic in `B`.

The current five-field `UnitChoices.dimScale` is the `PhyslibBase` instance of this
fold, written out by hand; `UnitChoices.toScale` exhibits the correspondence.

-/

@[expose] public section

open NNReal
open scoped BigOperators

/-- A choice of unit for each base dimension of `B`: a positive-real magnitude per
  base. This is the basis-generic form of `UnitChoices`. -/
structure UnitScale (B : Type) where
  /-- The positive-real magnitude of the chosen unit at each base dimension. -/
  scale : B → ℝ≥0
  /-- Each chosen unit has a positive magnitude. -/
  scale_pos : ∀ b, 0 < scale b

namespace UnitScale

variable {B : Type}

lemma ratio_ne_zero (u1 u2 : UnitScale B) (b : B) : u1.scale b / u2.scale b ≠ 0 :=
  (div_pos (u1.scale_pos b) (u2.scale_pos b)).ne'

/-- The dimension-scaling homomorphism, generic in the basis `B`: a quantity of
  dimension `d` rescales by `∏ b, (u1 b / u2 b) ^ d.exponent b` when changing the
  unit choice from `u1` to `u2`. This is the basis-generic form of
  `UnitChoices.dimScale`. -/
noncomputable def dimScale [Fintype B] (u1 u2 : UnitScale B) : Dimension B →* ℝ≥0 where
  toFun d := ∏ b, (u1.scale b / u2.scale b) ^ (d.exponent b : ℝ)
  map_one' := by simp
  map_mul' d1 d2 := by
    simp only [Dimension.mul_exponent, Rat.cast_add]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun b _ =>
      NNReal.rpow_add (u1.ratio_ne_zero u2 b) _ _

@[simp]
lemma dimScale_self [Fintype B] (u : UnitScale B) (d : Dimension B) :
    dimScale u u d = 1 := by
  simp only [dimScale, MonoidHom.coe_mk, OneHom.coe_mk]
  refine Finset.prod_eq_one fun b _ => ?_
  rw [div_self (u.scale_pos b).ne', NNReal.one_rpow]

@[simp]
lemma dimScale_one [Fintype B] (u1 u2 : UnitScale B) :
    dimScale u1 u2 1 = 1 := map_one _

/-- The scaling is transitive (a cocycle in the unit choices). -/
lemma dimScale_transitive [Fintype B] (u1 u2 u3 : UnitScale B) (d : Dimension B) :
    dimScale u1 u2 d * dimScale u2 u3 d = dimScale u1 u3 d := by
  simp only [dimScale, MonoidHom.coe_mk, OneHom.coe_mk, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [← NNReal.mul_rpow]
  congr 1
  rw [div_mul_div_comm, mul_comm (u2.scale b), mul_div_mul_right _ _ (u2.scale_pos b).ne']

end UnitScale

/-!
## The current five-field `UnitChoices` is the `PhyslibBase` instance

`UnitChoices.toScale` reads the five typed units as a `UnitScale PhyslibBase`,
exhibiting the existing bespoke `dimScale` as the `PhyslibBase` case of the generic
fold.
-/

namespace UnitChoices

/-- Read a five-field `UnitChoices` as a `UnitScale` over `PhyslibBase`. -/
noncomputable def toScale (u : UnitChoices) : UnitScale PhyslibBase where
  scale
    | .length => ⟨u.length.val, u.length.val_pos.le⟩
    | .time => ⟨u.time.val, u.time.val_pos.le⟩
    | .mass => ⟨u.mass.val, u.mass.val_pos.le⟩
    | .charge => ⟨u.charge.val, u.charge.val_pos.le⟩
    | .temperature => ⟨u.temperature.val, u.temperature.val_pos.le⟩
  scale_pos b := by
    cases b
    · exact NNReal.coe_pos.mp u.length.val_pos
    · exact NNReal.coe_pos.mp u.time.val_pos
    · exact NNReal.coe_pos.mp u.mass.val_pos
    · exact NNReal.coe_pos.mp u.charge.val_pos
    · exact NNReal.coe_pos.mp u.temperature.val_pos

end UnitChoices
