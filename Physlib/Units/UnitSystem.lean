/-
Copyright (c) 2026 Nicolas Rouquette. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
module

public import Physlib.Units.ParametricUnits
/-!

# Typed unit systems, parametrised in a dimension basis

`Dimension B` is basis-generic and `ParametricUnits` gives the basis-generic *magnitude*
layer `UnitScale B` (a positive real per base dimension, with the scaling homomorphism
`UnitScale.dimScale` proved once via `Finset.prod`). What was still hardwired to the
default basis is the *typed* unit side: `LTMCTUnitChoices` is a bespoke five-field record with
one named unit type per base dimension (`LengthUnit`, `TimeUnit`, …).

This module provides the generic typed layer. A `UnitSystem B` attaches to a basis `B` a
family of *typed* unit types — one per base dimension — each carrying a positive-real
magnitude:

* `UnitSystem B` — the class: `Unit : B → Type`, `mag`, `mag_pos`.
* `TypedChoice B` — a typed unit at every base dimension, `(b : B) → UnitSystem.Unit b`.
* `TypedChoice.toScale : TypedChoice B → UnitScale B` — forget the types down to the
  magnitude layer already provided by `ParametricUnits`.

The `LTMCTDimensionBase` instance recovers exactly today's typed unit names, and
`LTMCTUnitChoices ≃ TypedChoice LTMCTDimensionBase` exhibits the bespoke five-field record as
that instance. The scaling laws are **not** re-proved here: they live once on the
magnitude layer `UnitScale B`, and the typed layer is a thin faithful wrapper projecting
onto it via `toScale`.

This is the typed, basis-generic layer discussed as "Option D" in the review of the
dimension-parametrisation PR; it is the only design that keeps *both* basis-genericity
and typed-unit safety.

-/

@[expose] public section

open NNReal
open scoped BigOperators

/-- A **typed unit system** for a basis `B`: for each base dimension `b : B`, a typed
  unit type `Unit b`, together with the positive-real magnitude `mag` of each such unit.
  This is the data that makes a *typed* unit choice over `B` (as opposed to the bare
  magnitude layer `UnitScale B`) possible for an arbitrary basis. -/
class UnitSystem (B : Type) where
  /-- The typed unit type at each base dimension. -/
  Unit : B → Type
  /-- The positive-real magnitude of a typed unit. -/
  mag : {b : B} → Unit b → ℝ≥0
  /-- Every typed unit has a positive magnitude. -/
  mag_pos : ∀ {b : B} (u : Unit b), 0 < mag u

namespace UnitSystem

variable {B : Type}

end UnitSystem

/-- A **typed unit choice** over a basis `B` equipped with a `UnitSystem`: a typed unit
  at every base dimension. This is the basis-generic, *typed* form of `LTMCTUnitChoices`. -/
def TypedChoice (B : Type) [UnitSystem B] := (b : B) → UnitSystem.Unit b

namespace TypedChoice

variable {B : Type} [UnitSystem B]

/-- Forget a typed unit choice down to its magnitude layer `UnitScale B`, the layer on
  which the scaling homomorphism `UnitScale.dimScale` is already proved. -/
noncomputable def toScale (u : TypedChoice B) : UnitScale B where
  scale b := UnitSystem.mag (u b)
  scale_pos b := UnitSystem.mag_pos (u b)

@[simp]
lemma toScale_scale (u : TypedChoice B) (b : B) :
    (toScale u).scale b = UnitSystem.mag (u b) := rfl

end TypedChoice

/-!

## The `LTMCTDimensionBase` instance

The default basis's `UnitSystem` recovers exactly PhysLib's five named typed unit types,
so `TypedChoice LTMCTDimensionBase` is the typed five-slot unit choice and
`u .length : LengthUnit`, `LengthUnit.meters`, … all still work — and a `MassUnit` cannot
be placed in the length slot.

-/

noncomputable instance : UnitSystem LTMCTDimensionBase where
  Unit
    | .length => LengthUnit
    | .time => TimeUnit
    | .mass => MassUnit
    | .charge => ChargeUnit
    | .temperature => TemperatureUnit
  mag {b} :=
    match b with
    | .length | .time | .mass | .charge | .temperature => fun u => ⟨u.val, u.val_pos.le⟩
  mag_pos {b} :=
    match b with
    | .length | .time | .mass | .charge | .temperature => fun u => NNReal.coe_pos.mp u.val_pos

/-- Type-safety check: a typed unit choice over `LTMCTDimensionBase` projects onto the
  named typed unit types, so the length slot is a `LengthUnit` (and cannot hold a
  `MassUnit`). -/
example (u : TypedChoice LTMCTDimensionBase) : LengthUnit := u .length

example : TypedChoice LTMCTDimensionBase := fun
  | .length => LengthUnit.meters
  | .time => TimeUnit.seconds
  | .mass => MassUnit.kilograms
  | .charge => ChargeUnit.coulombs
  | .temperature => TemperatureUnit.kelvin

/-!

## `LTMCTUnitChoices` is `TypedChoice LTMCTDimensionBase`

The bespoke five-field record and the generic typed choice over the default basis carry
the same data.

-/

namespace LTMCTUnitChoices

/-- The bespoke five-field `LTMCTUnitChoices` and the generic `TypedChoice LTMCTDimensionBase`
  are the same data. -/
def equivTypedChoice : LTMCTUnitChoices ≃ TypedChoice LTMCTDimensionBase where
  toFun u := fun
    | .length => u.length
    | .time => u.time
    | .mass => u.mass
    | .charge => u.charge
    | .temperature => u.temperature
  invFun f :=
    { length := f .length
      time := f .time
      mass := f .mass
      charge := f .charge
      temperature := f .temperature }
  left_inv u := by cases u; rfl
  right_inv f := by funext b; cases b <;> rfl

/-- The typed generic projection agrees with the bespoke `LTMCTUnitChoices.toScale`: reading
  `LTMCTUnitChoices` as a `TypedChoice` and forgetting to the magnitude layer is the same as
  the bespoke `toScale`. -/
lemma toScale_equivTypedChoice (u : LTMCTUnitChoices) :
    (equivTypedChoice u).toScale = u.toScale := by
  refine UnitScale.ext ?_
  funext b
  cases b <;> rfl

end LTMCTUnitChoices

/-!

## The bespoke scaling law is the generic fold

`LTMCTUnitChoices.dimScale` — the five explicit `rpow` factors written out by hand in
`Basic.lean` — is exactly the generic `UnitScale.dimScale` fold (a `Finset.prod` over the
basis) at the `LTMCTDimensionBase` instance, applied to `toScale`. This is what makes the
typed layer a *faithful* wrapper rather than a second, independent statement of the
scaling law: there is one source of truth, the generic fold on `UnitScale B`.

-/

open Finset in
private lemma prod_univ_LTMCTDimensionBase {M : Type} [CommMonoid M]
    (f : LTMCTDimensionBase → M) :
    ∏ b, f b = f .length * f .time * f .mass * f .charge * f .temperature := by
  rw [show (univ : Finset LTMCTDimensionBase)
        = {.length, .time, .mass, .charge, .temperature} from by decide]
  rw [prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_insert (by decide), prod_singleton, ← mul_assoc, ← mul_assoc, ← mul_assoc]

namespace LTMCTUnitChoices

private lemma length_ratio (u1 u2 : LTMCTUnitChoices) :
    u1.length / u2.length = u1.toScale.scale .length / u2.toScale.scale .length := by
  apply NNReal.eq; rw [LengthUnit.div_eq_val, NNReal.coe_div]; rfl

private lemma time_ratio (u1 u2 : LTMCTUnitChoices) :
    u1.time / u2.time = u1.toScale.scale .time / u2.toScale.scale .time := by
  apply NNReal.eq; rw [TimeUnit.div_eq_val, NNReal.coe_div]; rfl

private lemma mass_ratio (u1 u2 : LTMCTUnitChoices) :
    u1.mass / u2.mass = u1.toScale.scale .mass / u2.toScale.scale .mass := by
  apply NNReal.eq; rw [MassUnit.div_eq_val, NNReal.coe_div]; rfl

private lemma charge_ratio (u1 u2 : LTMCTUnitChoices) :
    u1.charge / u2.charge = u1.toScale.scale .charge / u2.toScale.scale .charge := by
  apply NNReal.eq; rw [ChargeUnit.div_eq_val, NNReal.coe_div]; rfl

private lemma temperature_ratio (u1 u2 : LTMCTUnitChoices) :
    u1.temperature / u2.temperature =
      u1.toScale.scale .temperature / u2.toScale.scale .temperature := by
  apply NNReal.eq; rw [TemperatureUnit.div_eq_val, NNReal.coe_div]; rfl

/-- The hand-rolled five-factor `LTMCTUnitChoices.dimScale` equals the basis-generic
  `UnitScale.dimScale` fold at `LTMCTDimensionBase`, applied to `toScale`. The scaling law
  therefore has a single source of truth on the magnitude layer `UnitScale B`. -/
lemma dimScale_eq_toScale_dimScale (u1 u2 : LTMCTUnitChoices) (d : Dimension LTMCTDimensionBase) :
    u1.dimScale u2 d = UnitScale.dimScale u1.toScale u2.toScale d := by
  rw [dimScale_apply, length_ratio, time_ratio, mass_ratio, charge_ratio, temperature_ratio,
    UnitScale.dimScale, MonoidHom.coe_mk, OneHom.coe_mk, prod_univ_LTMCTDimensionBase]
  simp only [Dimension.length, Dimension.time, Dimension.mass, Dimension.charge,
    Dimension.temperature]

end LTMCTUnitChoices
