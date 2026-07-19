/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Tactic.DeriveFintype
/-!

# Dimension

In this module we define the type `Dimension` which carries the dimension
of a physical quantity.

A `Dimension B` is parameterised by a *basis* `B` of base dimensions: it assigns a
rational `exponent` to each base dimension `b : B`. PhysLib's default basis is
`PhyslibBase`, whose five base dimensions are length, time, mass, charge and
temperature; `Dimension PhyslibBase` recovers the familiar five-exponent dimension,
and its `length`, `time`, `mass`, `charge` and `temperature` projections are
provided so that existing code is unaffected. Note that this basis is *charge*-based
and has five generators, so it is **not** the SI/ISQ base-quantity set (which takes
electric current as base and adds amount of substance and luminous intensity). The
ISQ, Gaussian–CGS, natural-unit, and angle-augmented systems are other
instantiations `Dimension B` for a different basis `B`.

The parameterisation is purely in the dimensional *algebra*: `Dimension B` is a
`CommGroup` for every `B` (multiplication adds exponents, inversion negates them),
so quantities can be typed by dimensions over any basis. The commutative-group and
`ℚ`-power structure, decidable equality (`DecidableEq`), and the base vectors
`single b` are all generic in `B`.

-/

@[expose] public section

open NNReal

/-!

## The PhysLib base

-/

/-- PhysLib's default basis of base dimensions — `length`, `time`, `mass`,
  `charge`, `temperature`. Note this is *charge*-based, so it is not the SI/ISQ
  base-quantity set; see `Dimension`. -/
inductive PhyslibBase where
  /-- The length base dimension. -/
  | length
  /-- The time base dimension. -/
  | time
  /-- The mass base dimension. -/
  | mass
  /-- The charge base dimension. -/
  | charge
  /-- The temperature base dimension. -/
  | temperature
deriving DecidableEq, Fintype

/-!

## Defining dimensions

-/

/-- A dimension over a basis `B` of base dimensions: a rational `exponent` for each
  base dimension `b : B`. PhysLib's default basis is `PhyslibBase`. -/
structure Dimension (B : Type) where
  /-- The exponent of each base dimension. -/
  exponent : B → ℚ

namespace Dimension

variable {B : Type}

@[ext]
lemma ext {d1 d2 : Dimension B} (h : ∀ b, d1.exponent b = d2.exponent b) : d1 = d2 := by
  cases d1
  cases d2
  congr
  funext b
  exact h b

instance : Mul (Dimension B) where
  mul d1 d2 := ⟨fun b => d1.exponent b + d2.exponent b⟩

@[simp]
lemma mul_exponent (d1 d2 : Dimension B) (b : B) :
    (d1 * d2).exponent b = d1.exponent b + d2.exponent b := rfl

instance : One (Dimension B) where
  one := ⟨fun _ => 0⟩

@[simp]
lemma one_exponent (b : B) : (1 : Dimension B).exponent b = 0 := rfl

instance : CommGroup (Dimension B) where
  mul_assoc a b c := by
    ext x
    simp [add_assoc]
  one_mul a := by
    ext x
    simp
  mul_one a := by
    ext x
    simp
  inv d := ⟨fun b => -d.exponent b⟩
  inv_mul_cancel a := by
    ext x
    simp
  mul_comm a b := by
    ext x
    simp [add_comm]

@[simp]
lemma inv_exponent (d : Dimension B) (b : B) : d⁻¹.exponent b = -d.exponent b := rfl

@[simp]
lemma div_exponent (d1 d2 : Dimension B) (b : B) :
    (d1 / d2).exponent b = d1.exponent b - d2.exponent b := by
  simp [div_eq_mul_inv, sub_eq_add_neg]

@[simp]
lemma npow_exponent (d : Dimension B) (n : ℕ) (b : B) :
    (d ^ n).exponent b = n • d.exponent b := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_exponent, ih, succ_nsmul]

instance : Pow (Dimension B) ℚ where
  pow d q := ⟨fun b => d.exponent b * q⟩

@[simp]
lemma qpow_exponent (d : Dimension B) (q : ℚ) (b : B) :
    (d ^ q).exponent b = d.exponent b * q := rfl

/-- Decidable equality of dimensions over a finite basis `B`. -/
instance [Fintype B] : DecidableEq (Dimension B) := fun d1 d2 =>
  decidable_of_iff (∀ b, d1.exponent b = d2.exponent b)
    ⟨fun h => Dimension.ext h, fun h _ => h ▸ rfl⟩

/-- The base-dimension vector for `b : B`: exponent `1` at `b`, `0` elsewhere. This
  is the generic analogue of the named generators `L𝓭`, `T𝓭`, … -/
def single [DecidableEq B] (b : B) : Dimension B := ⟨Pi.single b 1⟩

@[simp]
lemma single_exponent [DecidableEq B] (b b' : B) :
    (single b).exponent b' = if b' = b then 1 else 0 := by
  simp only [single, Pi.single_apply]

/-- Change of basis along a map `f : B → B'` of base dimensions: reindex a dimension
  over `B` into one over `B'` by placing each exponent at its image. For an embedding
  `f` (injective) this preserves every exponent (`extend_exponent_apply`), so a
  dimension in one system re-expresses faithfully in an extending one. -/
def extend {B' : Type} [Fintype B] [DecidableEq B'] (f : B → B') (d : Dimension B) :
    Dimension B' :=
  ⟨fun b' => ∑ b, if f b = b' then d.exponent b else 0⟩

@[simp]
lemma extend_exponent_apply {B' : Type} [Fintype B] [DecidableEq B'] {f : B → B'}
    (hf : Function.Injective f) (d : Dimension B) (b : B) :
    (extend f d).exponent (f b) = d.exponent b := by
  simp only [extend]
  rw [Finset.sum_eq_single b (fun b'' _ hne => by simp [hf.ne hne]) (by simp)]
  simp

/-!

## The PhyslibBase projections

The five base-dimension exponents of a `Dimension PhyslibBase`, provided so that
the familiar `.length`, `.time`, `.mass`, `.charge`, `.temperature` API is available.

-/

/-- The length exponent of a `PhyslibBase` dimension. -/
def length (d : Dimension PhyslibBase) : ℚ := d.exponent .length
/-- The time exponent of a `PhyslibBase` dimension. -/
def time (d : Dimension PhyslibBase) : ℚ := d.exponent .time
/-- The mass exponent of a `PhyslibBase` dimension. -/
def mass (d : Dimension PhyslibBase) : ℚ := d.exponent .mass
/-- The charge exponent of a `PhyslibBase` dimension. -/
def charge (d : Dimension PhyslibBase) : ℚ := d.exponent .charge
/-- The temperature exponent of a `PhyslibBase` dimension. -/
def temperature (d : Dimension PhyslibBase) : ℚ := d.exponent .temperature

/-- Build a `PhyslibBase` dimension from its five exponents, in the order
  `⟨length, time, mass, charge, temperature⟩`. -/
def ofPhyslibBase (length time mass charge temperature : ℚ) : Dimension PhyslibBase :=
  ⟨fun
    | .length => length
    | .time => time
    | .mass => mass
    | .charge => charge
    | .temperature => temperature⟩

@[simp]
lemma ofPhyslibBase_length (l t m c θ : ℚ) : (ofPhyslibBase l t m c θ).length = l := rfl

@[simp]
lemma ofPhyslibBase_time (l t m c θ : ℚ) : (ofPhyslibBase l t m c θ).time = t := rfl

@[simp]
lemma ofPhyslibBase_mass (l t m c θ : ℚ) : (ofPhyslibBase l t m c θ).mass = m := rfl

@[simp]
lemma ofPhyslibBase_charge (l t m c θ : ℚ) : (ofPhyslibBase l t m c θ).charge = c := rfl

@[simp]
lemma ofPhyslibBase_temperature (l t m c θ : ℚ) : (ofPhyslibBase l t m c θ).temperature = θ := rfl

@[simp]
lemma time_mul (d1 d2 : Dimension PhyslibBase) :
    (d1 * d2).time = d1.time + d2.time := rfl

@[simp]
lemma length_mul (d1 d2 : Dimension PhyslibBase) :
    (d1 * d2).length = d1.length + d2.length := rfl

@[simp]
lemma mass_mul (d1 d2 : Dimension PhyslibBase) :
    (d1 * d2).mass = d1.mass + d2.mass := rfl

@[simp]
lemma charge_mul (d1 d2 : Dimension PhyslibBase) :
    (d1 * d2).charge = d1.charge + d2.charge := rfl

@[simp]
lemma temperature_mul (d1 d2 : Dimension PhyslibBase) :
    (d1 * d2).temperature = d1.temperature + d2.temperature := rfl

@[simp]
lemma one_length : (1 : Dimension PhyslibBase).length = 0 := rfl
@[simp]
lemma one_time : (1 : Dimension PhyslibBase).time = 0 := rfl

@[simp]
lemma one_mass : (1 : Dimension PhyslibBase).mass = 0 := rfl

@[simp]
lemma one_charge : (1 : Dimension PhyslibBase).charge = 0 := rfl

@[simp]
lemma one_temperature : (1 : Dimension PhyslibBase).temperature = 0 := rfl

@[simp]
lemma inv_length (d : Dimension PhyslibBase) : d⁻¹.length = -d.length := rfl

@[simp]
lemma inv_time (d : Dimension PhyslibBase) : d⁻¹.time = -d.time := rfl

@[simp]
lemma inv_mass (d : Dimension PhyslibBase) : d⁻¹.mass = -d.mass := rfl

@[simp]
lemma inv_charge (d : Dimension PhyslibBase) : d⁻¹.charge = -d.charge := rfl

@[simp]
lemma inv_temperature (d : Dimension PhyslibBase) : d⁻¹.temperature = -d.temperature := rfl

@[simp]
lemma div_length (d1 d2 : Dimension PhyslibBase) : (d1 / d2).length = d1.length - d2.length := by
  simp only [length, div_exponent]

@[simp]
lemma div_time (d1 d2 : Dimension PhyslibBase) : (d1 / d2).time = d1.time - d2.time := by
  simp only [time, div_exponent]

@[simp]
lemma div_mass (d1 d2 : Dimension PhyslibBase) : (d1 / d2).mass = d1.mass - d2.mass := by
  simp only [mass, div_exponent]

@[simp]
lemma div_charge (d1 d2 : Dimension PhyslibBase) : (d1 / d2).charge = d1.charge - d2.charge := by
  simp only [charge, div_exponent]

@[simp]
lemma div_temperature (d1 d2 : Dimension PhyslibBase) :
    (d1 / d2).temperature = d1.temperature - d2.temperature := by
  simp only [temperature, div_exponent]

@[simp]
lemma npow_length (d : Dimension PhyslibBase) (n : ℕ) : (d ^ n).length = n • d.length := by
  simp only [length, npow_exponent]

@[simp]
lemma npow_time (d : Dimension PhyslibBase) (n : ℕ) : (d ^ n).time = n • d.time := by
  simp only [time, npow_exponent]

@[simp]
lemma npow_mass (d : Dimension PhyslibBase) (n : ℕ) : (d ^ n).mass = n • d.mass := by
  simp only [mass, npow_exponent]

@[simp]
lemma npow_charge (d : Dimension PhyslibBase) (n : ℕ) : (d ^ n).charge = n • d.charge := by
  simp only [charge, npow_exponent]

@[simp]
lemma npow_temperature (d : Dimension PhyslibBase) (n : ℕ) :
    (d ^ n).temperature = n • d.temperature := by
  simp only [temperature, npow_exponent]

/-- The dimension corresponding to length. -/
def L𝓭 : Dimension PhyslibBase := ofPhyslibBase 1 0 0 0 0

@[simp]
lemma L𝓭_length : L𝓭.length = 1 := by rfl

@[simp]
lemma L𝓭_time : L𝓭.time = 0 := by rfl

@[simp]
lemma L𝓭_mass : L𝓭.mass = 0 := by rfl

@[simp]
lemma L𝓭_charge : L𝓭.charge = 0 := by rfl

@[simp]
lemma L𝓭_temperature : L𝓭.temperature = 0 := by rfl

/-- The dimension corresponding to time. -/
def T𝓭 : Dimension PhyslibBase := ofPhyslibBase 0 1 0 0 0

@[simp]
lemma T𝓭_length : T𝓭.length = 0 := by rfl

@[simp]
lemma T𝓭_time : T𝓭.time = 1 := by rfl

@[simp]
lemma T𝓭_mass : T𝓭.mass = 0 := by rfl

@[simp]
lemma T𝓭_charge : T𝓭.charge = 0 := by rfl

@[simp]
lemma T𝓭_temperature : T𝓭.temperature = 0 := by rfl

/-- The dimension corresponding to mass. -/
def M𝓭 : Dimension PhyslibBase := ofPhyslibBase 0 0 1 0 0

/-- The dimension corresponding to charge. -/
def C𝓭 : Dimension PhyslibBase := ofPhyslibBase 0 0 0 1 0

/-- The dimension corresponding to temperature. -/
def Θ𝓭 : Dimension PhyslibBase := ofPhyslibBase 0 0 0 0 1

/-!

## The named generators are the base vectors

Each named generator `L𝓭`, `T𝓭`, … is the generic `single` base vector at the
corresponding base dimension, exhibiting them as instances of the basis-generic API.

-/

lemma L𝓭_eq_single : L𝓭 = single .length := by
  ext b; cases b <;> simp [L𝓭, ofPhyslibBase, single_exponent]

lemma T𝓭_eq_single : T𝓭 = single .time := by
  ext b; cases b <;> simp [T𝓭, ofPhyslibBase, single_exponent]

lemma M𝓭_eq_single : M𝓭 = single .mass := by
  ext b; cases b <;> simp [M𝓭, ofPhyslibBase, single_exponent]

lemma C𝓭_eq_single : C𝓭 = single .charge := by
  ext b; cases b <;> simp [C𝓭, ofPhyslibBase, single_exponent]

lemma Θ𝓭_eq_single : Θ𝓭 = single .temperature := by
  ext b; cases b <;> simp [Θ𝓭, ofPhyslibBase, single_exponent]

end Dimension
