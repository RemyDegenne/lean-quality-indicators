/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupTheory.UnitriangularLowerCentralSeries
public import Mathlib.GroupTheory.Solvable

/-!
# Derived series of finite unitriangular groups

The commutator of two positive stages of the superdiagonal filtration is
exactly the stage indexed by their sum. Consequently the native derived
series consists of the stages indexed by powers of two, over any commutative
ring, including the zero ring.

## References

- Mathlib contributors, `Mathlib.GroupTheory.Solvable` (the derived series),
  `Mathlib.GroupTheory.Commutator.Basic` (subgroup commutators) and
  `Mathlib.GroupTheory.Nilpotent` (the lower central series used for the
  stopping criterion).
- General Linear Groups contributors, `GeneralLinearGroups.ElementaryCommutator`
  (the elementary-unit relation used through the preceding modules).
-/

@[expose] public section

open scoped commutatorElement

namespace Matrix.UnitriangularGroup

variable (n : ℕ) (R : Type) [CommRing R]

/-- The commutator of two positive superdiagonal stages is their sum stage.
The reverse inclusion uses the elementary-unit relation from
`GeneralLinearGroups.ElementaryCommutator` and the preceding generation
criterion, rather than a quotient of group schemes. -/
theorem superdiagonalSubgroup_commutator_eq (r s : ℕ)
    (hr : 1 ≤ r) (hs : 1 ≤ s) :
    ⁅superdiagonalSubgroup n R r, superdiagonalSubgroup n R s⁆ =
      superdiagonalSubgroup n R (r + s) := by
  apply le_antisymm (superdiagonalSubgroup_commutator n R r s)
  apply superdiagonalSubgroup_le_of_elementary_mem n R (r + s) (by omega)
  intro i j hij a hdist
  let k : Fin n := ⟨i.val + r, by have := j.isLt; omega⟩
  have hik : i < k := Fin.lt_def.mpr (by dsimp [k]; omega)
  have hkj : k < j := Fin.lt_def.mpr (by dsimp [k]; omega)
  have hfirst := elementary_mem_superdiagonalSubgroup n R i k hik a r
    (by dsimp [k]; omega)
  have hsecond := elementary_mem_superdiagonalSubgroup n R k j hkj (1 : R) s
    (by dsimp [k]; omega)
  have hcomm := Subgroup.commutator_mem_commutator hfirst hsecond
  have hroot := elementary_commutator n R i k j hik hkj a (1 : R)
  simpa only [hroot, mul_one] using hcomm

/-- The native derived series is the superdiagonal filtration at powers of two.
This uses Mathlib's `derivedSeries` successor and the positive-stage
commutator equality above. -/
theorem derivedSeries_eq_superdiagonalSubgroup (t : ℕ) :
    derivedSeries (Matrix.UnitriangularGroup (Fin n) R) t =
      superdiagonalSubgroup n R (2 ^ t) := by
  induction t with
  | zero =>
      simpa only [derivedSeries_zero, pow_zero] using
        (superdiagonalSubgroup_one n R).symm
  | succ t ih =>
      have hpos : 1 ≤ (2 : ℕ) ^ t := by
        have : 0 < (2 : ℕ) ^ t := by positivity
        omega
      rw [derivedSeries_succ, ih,
        superdiagonalSubgroup_commutator_eq n R (2 ^ t) (2 ^ t)
          hpos hpos]
      simp only [pow_succ, mul_two]

/-- Over a nontrivial ring, a positive stage is trivial exactly at or beyond
the dimension. The numerical criterion does not extend to the zero ring. -/
theorem superdiagonalSubgroup_eq_bot_iff [Nontrivial R] (d : ℕ) (hd : 1 ≤ d) :
    superdiagonalSubgroup n R d = ⊥ ↔ n ≤ d := by
  constructor
  · intro hbot
    have hseries :
        (⊤ : Subgroup (Matrix.UnitriangularGroup (Fin n) R)).lowerCentralSeries
          (d - 1) = ⊥ := by
      rw [lowerCentralSeries_eq_superdiagonalSubgroup n R (d - 1),
        Nat.sub_add_cancel hd]
      exact hbot
    have hclass := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp hseries
    rw [nilpotencyClass_eq_of_nontrivial n R] at hclass
    omega
  · intro hle
    apply le_antisymm _ bot_le
    rw [← superdiagonalSubgroup_end n R]
    exact superdiagonalSubgroup_antitone n R hle

/-- Over a nontrivial ring, the native derived series stops exactly when its
superdiagonal stage reaches the dimension, using Mathlib's `derivedSeries`
and the preceding point-group class and lower-central-series criteria. -/
theorem derivedSeries_eq_bot_iff [Nontrivial R] (t : ℕ) :
    derivedSeries (Matrix.UnitriangularGroup (Fin n) R) t = ⊥ ↔ n ≤ 2 ^ t := by
  rw [derivedSeries_eq_superdiagonalSubgroup n R t]
  apply superdiagonalSubgroup_eq_bot_iff n R (2 ^ t)
  have : 0 < (2 : ℕ) ^ t := by positivity
  omega

end Matrix.UnitriangularGroup
