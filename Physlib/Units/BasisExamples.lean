/-
Copyright (c) 2026 Nicolas Rouquette. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
module

public import Physlib.Units.Dimension
/-!

# Worked instantiations: the motivating quantity systems

`Dimension` is parametric over a basis `B` of base dimensions, so quantity systems
that the fixed five-field record cannot express become ordinary instantiations
`Dimension B`. This module realises the four systems that motivate the parametric
API and checks the defining relations of each:

* **ISQ** — the seven ISO/IEC 80000-1 base quantities, with *electric current* as
  base (charge derived) and *amount of substance* and *luminous intensity* added.
* **Gaussian–CGS** — three generators `L, M, T`, with electric charge the *derived*
  rational vector `M^(1/2)·L^(3/2)·T^(-1)`.
* **Natural units** — `c = ħ = 1`, a single generator, with length and time both of
  dimension `mass⁻¹`.
* **Angle-augmented** — an added `angle` generator, with *solid angle* the derived
  square `angle²` (`sr = rad²`).

Each basis is a `Fintype` with `DecidableEq`, so the generic `CommGroup`, `ℚ`-power,
`single` base vectors, and `DecidableEq (Dimension B)` all apply unchanged.

This module is illustrative and should not be imported by other modules.

-/

@[expose] public section

open Dimension

namespace BasisExamples

/-!
## ISQ — the seven ISO/IEC 80000-1 base quantities (current-based)
-/

/-- The seven ISQ base quantities: length, time, mass, electric current, temperature,
  amount of substance, luminous intensity. Unlike `PhyslibBase`, current is base and
  charge is derived. -/
inductive ISQBase
  | length | time | mass | current | temperature | amount | luminousIntensity
  deriving DecidableEq, Fintype

namespace ISQ

/-- The ISQ has seven base quantities. -/
example : Fintype.card ISQBase = 7 := by decide

/-- Electric charge is *derived* in the ISQ: `Q = I · T`. -/
def charge : Dimension ISQBase := single .current * single .time

example : charge.exponent .current = 1 := by simp [charge, single_exponent]
example : charge.exponent .time = 1 := by simp [charge, single_exponent]
example : charge.exponent .mass = 0 := by simp [charge, single_exponent]

/-- Amount of substance is an independent base dimension (absent from `PhyslibBase`). -/
example : (single (.amount : ISQBase)) ≠ 1 := by
  intro h
  have := congrArg (fun d => Dimension.exponent d .amount) h
  simp [single_exponent] at this

/-- Luminous intensity is an independent base dimension (absent from `PhyslibBase`). -/
example : (single (.luminousIntensity : ISQBase)) ≠ 1 := by
  intro h
  have := congrArg (fun d => Dimension.exponent d .luminousIntensity) h
  simp [single_exponent] at this

end ISQ

/-!
## Gaussian–CGS — three generators, charge derived with half-integer exponents
-/

/-- Gaussian–CGS has three generators: length, mass, time. -/
inductive GaussianBase
  | length | mass | time
  deriving DecidableEq, Fintype

namespace Gaussian

/-- Gaussian–CGS has three base dimensions. -/
example : Fintype.card GaussianBase = 3 := by decide

/-- Gaussian electric charge is the *derived* dimension `M^(1/2)·L^(3/2)·T^(-1)` —
  the half-integer exponents that make `Dimension`'s `ℚ` exponents necessary. -/
def charge : Dimension GaussianBase :=
  single .mass ^ (1 / 2 : ℚ) * single .length ^ (3 / 2 : ℚ) * single .time ^ (-1 : ℚ)

example : charge.exponent .mass = 1 / 2 := by simp [charge, single_exponent]
example : charge.exponent .length = 3 / 2 := by simp [charge, single_exponent]
example : charge.exponent .time = -1 := by simp [charge, single_exponent]

end Gaussian

/-!
## Natural units — `c = ħ = 1`, a single generator
-/

/-- With `c = ħ = 1` every dimension is a power of a single generator (mass). -/
inductive NaturalBase
  | mass
  deriving DecidableEq, Fintype

namespace Natural

/-- A natural-unit system has a single base dimension. -/
example : Fintype.card NaturalBase = 1 := by decide

/-- Energy/mass is the single generator. -/
abbrev mass : Dimension NaturalBase := single .mass

/-- With `c = ħ = 1`, length has dimension `mass⁻¹`. -/
def length : Dimension NaturalBase := mass ^ (-1 : ℚ)
/-- With `c = ħ = 1`, time also has dimension `mass⁻¹`. -/
def time : Dimension NaturalBase := mass ^ (-1 : ℚ)

/-- Length and time carry the *same* dimension in natural units — the identification
  the fixed basis cannot express. -/
example : length = time := rfl

end Natural

/-!
## Angle-augmented — solid angle is the square of plane angle (`sr = rad²`)
-/

/-- `PhyslibBase` augmented with a plane-`angle` generator. -/
inductive AngleBase
  | length | time | mass | charge | temperature | angle
  deriving DecidableEq, Fintype

namespace Angle

/-- Plane angle as its own base dimension. -/
abbrev angle : Dimension AngleBase := single .angle

/-- Solid angle is the *square* of plane angle: `sr = rad²`. -/
def solidAngle : Dimension AngleBase := angle ^ 2

example : solidAngle = angle * angle := by rw [solidAngle, pow_two]

/-- The solid-angle dimension has exponent `2` over the `angle` generator. -/
example : solidAngle.exponent .angle = 2 := by simp [solidAngle, single_exponent]

end Angle

/-!
## Change of basis: embedding `PhyslibBase` into the angle-augmented basis

`Dimension.extend` re-expresses a dimension over one basis in an extending basis.
-/

/-- `PhyslibBase` embeds into the angle-augmented `AngleBase`. -/
def physlibToAngle : PhyslibBase → AngleBase
  | .length => .length
  | .time => .time
  | .mass => .mass
  | .charge => .charge
  | .temperature => .temperature

lemma physlibToAngle_injective : Function.Injective physlibToAngle := by
  intro a b h
  cases a <;> cases b <;> simp_all [physlibToAngle]

/-- A `PhyslibBase` dimension re-expresses faithfully in the extending basis: the
  length exponent is preserved by the change of basis. -/
example :
    (Dimension.extend physlibToAngle L𝓭).exponent (physlibToAngle .length) = 1 := by
  rw [Dimension.extend_exponent_apply physlibToAngle_injective]
  rfl

end BasisExamples
