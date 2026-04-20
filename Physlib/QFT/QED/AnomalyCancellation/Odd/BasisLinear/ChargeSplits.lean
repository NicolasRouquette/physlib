/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QED.AnomalyCancellation.BasisLinear
public import Physlib.QFT.QED.AnomalyCancellation.VectorLike
/-!
# Charge splits for the odd case basis
-/

@[expose] public section

open Module Nat Finset BigOperators

namespace PureU1

variable {n : ℕ}

namespace VectorLikeOddPlane

/-!

## A. Splitting the charges up into groups

We have `2 * n + 1` charges, which we split up in the following ways:

`| evenFst j (0 to n) | evenSnd j (n.succ to n + n.succ)|`

```
| evenShiftZero (0) | evenShiftFst j (1 to n) |
  evenShiftSnd j (n.succ to 2 * n) | evenShiftLast (2 * n.succ - 1) |
```

-/

section theDeltas

/-!

### A.1. The symmetric split: Spltting the charges up via `(n + 1) + 1`

-/

lemma odd_shift_eq (n : ℕ) : (1 + n) + n = 2 * n +1 := by
  omega

/-- The inclusion of `Fin n` into `Fin ((n + 1) + n)` via the first `n`.
  This is then casted to `Fin (2 * n + 1)`. -/
def oddFst (j : Fin n) : Fin (2 * n + 1) :=
  Fin.cast (split_odd n) (Fin.castAdd n (Fin.castAdd 1 j))

/-- The inclusion of `Fin n` into `Fin ((n + 1) + n)` via the second `n`.
  This is then casted to `Fin (2 * n + 1)`. -/
def oddSnd (j : Fin n) : Fin (2 * n + 1) :=
  Fin.cast (split_odd n) (Fin.natAdd (n+1) j)

/-- The element representing `1` in `Fin ((n + 1) + n)`.
  This is then casted to `Fin (2 * n + 1)`. -/
def oddMid : Fin (2 * n + 1) :=
  Fin.cast (split_odd n) (Fin.castAdd n (Fin.natAdd n 1))

lemma sum_odd (S : Fin (2 * n + 1) → ℚ) :
    ∑ i, S i = S oddMid + ∑ i : Fin n, ((S ∘ oddFst) i + (S ∘ oddSnd) i) := by
  have h1 : ∑ i, S i = ∑ i : Fin (n + 1 + n), S (Fin.cast (split_odd n) i) := by
    rw [Finset.sum_equiv (Fin.castOrderIso (split_odd n)).symm.toEquiv]
    · intro i
      simp only [mem_univ, Fin.symm_castOrderIso, RelIso.coe_fn_toEquiv]
    · exact fun _ _ => rfl
  rw [h1]
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [univ_unique, Fin.default_eq_zero, Fin.isValue, sum_singleton, Function.comp_apply]
  nth_rewrite 2 [add_comm]
  rw [add_assoc]
  rw [Finset.sum_add_distrib]
  rfl

/-!

### A.2. The shifted split: Spltting the charges up via `1 + n + n`

-/

/-- The inclusion of `Fin n` into `Fin (1 + n + n)` via the first `n`.
  This is then casted to `Fin (2 * n + 1)`. -/
def oddShiftFst (j : Fin n) : Fin (2 * n + 1) :=
  Fin.cast (odd_shift_eq n) (Fin.castAdd n (Fin.natAdd 1 j))

/-- The inclusion of `Fin n` into `Fin (1 + n + n)` via the second `n`.
  This is then casted to `Fin (2 * n + 1)`. -/
def oddShiftSnd (j : Fin n) : Fin (2 * n + 1) :=
  Fin.cast (odd_shift_eq n) (Fin.natAdd (1 + n) j)

/-- The element representing the `1` in `Fin (1 + n + n)`.
  This is then casted to `Fin (2 * n + 1)`. -/
def oddShiftZero : Fin (2 * n + 1) :=
  Fin.cast (odd_shift_eq n) (Fin.castAdd n (Fin.castAdd n 1))

lemma sum_oddShift (S : Fin (2 * n + 1) → ℚ) :
    ∑ i, S i = S oddShiftZero + ∑ i : Fin n, ((S ∘ oddShiftFst) i + (S ∘ oddShiftSnd) i) := by
  have h1 : ∑ i, S i = ∑ i : Fin ((1+n)+n), S (Fin.cast (odd_shift_eq n) i) := by
    rw [Finset.sum_equiv (Fin.castOrderIso (odd_shift_eq n)).symm.toEquiv]
    · intro i
      simp only [mem_univ, Fin.castOrderIso, RelIso.coe_fn_toEquiv]
    · exact fun _ _ => rfl
  rw [h1, Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [univ_unique, Fin.default_eq_zero, Fin.isValue, sum_singleton, Function.comp_apply]
  rw [add_assoc, Finset.sum_add_distrib]
  rfl

/-!

### A.3. The shifted shifted split: Spltting the charges up via `((1+n)+1) + n.succ`

-/

lemma odd_shift_shift_eq (n : ℕ) : ((1+n)+1) + n.succ = 2 * n.succ + 1 := by
  omega

/-- The element representing the first `1` in `Fin (1 + n + 1 + n.succ)` casted
  to `Fin (2 * n.succ + 1)`. -/
def oddShiftShiftZero : Fin (2 * n.succ + 1) :=
  Fin.cast (odd_shift_shift_eq n) (Fin.castAdd n.succ (Fin.castAdd 1 (Fin.castAdd n 1)))

/-- The inclusion of `Fin n` into `Fin (1 + n + 1 + n.succ)` via the first `n` and casted
  to `Fin (2 * n.succ + 1)`. -/
def oddShiftShiftFst (j : Fin n) : Fin (2 * n.succ + 1) :=
  Fin.cast (odd_shift_shift_eq n) (Fin.castAdd n.succ (Fin.castAdd 1 (Fin.natAdd 1 j)))

/-- The element representing the second `1` in `Fin (1 + n + 1 + n.succ)` casted
  to `2 * n.succ + 1`. -/
def oddShiftShiftMid : Fin (2 * n.succ + 1) :=
  Fin.cast (odd_shift_shift_eq n) (Fin.castAdd n.succ (Fin.natAdd (1+n) 1))

/-- The inclusion of `Fin n.succ` into `Fin (1 + n + 1 + n.succ)` via the `n.succ` and casted
  to `Fin (2 * n.succ + 1)`. -/
def oddShiftShiftSnd (j : Fin n.succ) : Fin (2 * n.succ + 1) :=
  Fin.cast (odd_shift_shift_eq n) (Fin.natAdd ((1+n)+1) j)

/-!

### A.4. Relating the splittings together

-/
lemma oddShiftShiftZero_eq_oddFst_zero : @oddShiftShiftZero n = oddFst 0 :=
  Fin.rev_inj.mp rfl

lemma oddShiftShiftZero_eq_oddShiftZero : @oddShiftShiftZero n = oddShiftZero := rfl

lemma oddShiftShiftFst_eq_oddFst_succ (j : Fin n) :
    oddShiftShiftFst j = oddFst j.succ := by
  rw [Fin.ext_iff]
  simp only [succ_eq_add_one, oddShiftShiftFst, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd,
    oddFst, Fin.val_succ]
  exact Nat.add_comm 1 ↑j

lemma oddShiftShiftFst_eq_oddShiftFst_castSucc (j : Fin n) :
    oddShiftShiftFst j = oddShiftFst j.castSucc := by
  rfl

lemma oddShiftShiftMid_eq_oddMid : @oddShiftShiftMid n = oddMid := by
  rw [Fin.ext_iff]
  simp only [succ_eq_add_one, oddShiftShiftMid, Fin.isValue, Fin.val_cast, Fin.val_castAdd,
    Fin.val_natAdd, Fin.val_eq_zero, add_zero, oddMid]
  exact Nat.add_comm 1 n

lemma oddShiftShiftMid_eq_oddShiftFst_last : oddShiftShiftMid = oddShiftFst (Fin.last n) := by
  rfl

lemma oddShiftShiftSnd_eq_oddSnd (j : Fin n.succ) : oddShiftShiftSnd j = oddSnd j := by
  rw [Fin.ext_iff]
  simp only [succ_eq_add_one, oddShiftShiftSnd, Fin.val_cast, Fin.val_natAdd, oddSnd, add_left_inj]
  exact Nat.add_comm 1 n

lemma oddShiftShiftSnd_eq_oddShiftSnd (j : Fin n.succ) : oddShiftShiftSnd j = oddShiftSnd j := by
  rw [Fin.ext_iff]
  rfl

lemma oddSnd_eq_oddShiftSnd (j : Fin n) : oddSnd j = oddShiftSnd j := by
  rw [Fin.ext_iff]
  simp only [oddSnd, Fin.val_cast, Fin.val_natAdd, oddShiftSnd, add_left_inj]
  exact Nat.add_comm n 1

lemma oddShiftZero_eq_oddFst : oddShiftZero = oddFst (0 : Fin n.succ) := by
  ext
  simp [oddShiftZero, oddFst]

lemma oddShiftFst_castSucc_eq_oddFst_succ (j : Fin n) :
    oddShiftFst j.castSucc = oddFst j.succ := by
  rw [Fin.ext_iff]
  simp only [oddShiftFst, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, oddFst, Fin.val_succ]
  exact Nat.add_comm 1 ↑j

lemma oddShiftFst_last_eq_oddMid : oddShiftFst (Fin.last n) = oddMid := by
  rw [Fin.ext_iff]
  simp only [oddShiftFst, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, oddMid, Fin.val_last]
  exact Nat.add_comm 1 n

lemma oddShiftSnd_eq_oddSnd (j : Fin n) : oddShiftSnd j = oddSnd j := by
  rw [Fin.ext_iff]
  simp only [oddShiftSnd, Fin.val_cast, Fin.val_natAdd, oddSnd, add_left_inj]
  ring

end theDeltas

end VectorLikeOddPlane

end PureU1
