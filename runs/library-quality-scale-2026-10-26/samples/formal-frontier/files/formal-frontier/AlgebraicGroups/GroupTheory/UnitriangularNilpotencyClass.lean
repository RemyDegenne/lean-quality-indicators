/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupTheory.UnitriangularCentralFiltration
public import GeneralLinearGroups.ElementaryCommutator

/-!
# Exact nilpotency class of finite unitriangular groups

Elementary units of the unitriangular subgroup realize nonzero elements of
its lower central series. Together with the superdiagonal upper bound this gives
the exact nilpotency class over every nontrivial commutative ring.
This is a numerical *point-group* result. Milne proves unitriangular
algebraic-group nilpotence by a central series, giving a field-based
point-group antecedent of nilpotence, but not this exact-class formula over
nontrivial commutative rings or its `Fin 0` boundary.

## References

- J. S. Milne, *Algebraic Groups* (2017), Example 6.36 and §6.49
  (central-series proof of unitriangular algebraic-group nilpotence, hence
  a field-based point-group nilpotence antecedent).
- General Linear Groups contributors, `GeneralLinearGroups.ElementaryCommutator`
  (`Matrix.GeneralLinearGroup.elementaryUnit_commutator`).
- Mathlib contributors, `Mathlib.GroupTheory.Nilpotent` (lower central series
  and nilpotency-class criteria) and the general-linear elementary-unit API.
-/

@[expose] public section

open scoped commutatorElement

namespace Matrix.UnitriangularGroup

variable (n : ℕ) (R : Type) [CommRing R]

/-- The elementary unit at a strictly upper-triangular position, in the unitriangular subgroup. -/
def elementary (i j : Fin n) (hij : i < j) (a : R) :
    Matrix.UnitriangularGroup (Fin n) R := by
  refine ⟨Matrix.GeneralLinearGroup.elementaryUnit i j (ne_of_lt hij) a, ?_⟩
  refine ⟨?_, ?_⟩
  · change (1 + Matrix.single i j a : Matrix (Fin n) (Fin n) R).IsUpperTriangular
    exact Matrix.blockTriangular_one.add (Matrix.blockTriangular_single hij.le a)
  · intro k
    change (1 + Matrix.single i j a : Matrix (Fin n) (Fin n) R) k k = 1
    have h : ¬ (i = k ∧ j = k) := fun h => (ne_of_lt hij) (h.1.trans h.2.symm)
    simp [Matrix.add_apply, h]

/-- The image of an elementary unit in the general linear group. -/
theorem elementary_gl (i j : Fin n) (hij : i < j) (a : R) :
    (elementary n R i j hij a).1 =
      Matrix.GeneralLinearGroup.elementaryUnit i j (ne_of_lt hij) a := rfl

/-- The matrix of an elementary unit. -/
theorem elementary_coe (i j : Fin n) (hij : i < j) (a : R) :
    ((elementary n R i j hij a).1 : Matrix (Fin n) (Fin n) R) =
      1 + Matrix.single i j a := rfl

/-- The ordered Steinberg commutator relation inside the unitriangular
group, transferred from `Matrix.GeneralLinearGroup.elementaryUnit_commutator`
in `GeneralLinearGroups.ElementaryCommutator`. -/
theorem elementary_commutator (i j k : Fin n)
    (hij : i < j) (hjk : j < k) (a b : R) :
    ⁅elementary n R i j hij a, elementary n R j k hjk b⁆ =
      elementary n R i k (lt_trans hij hjk) (a * b) := by
  apply Subtype.ext
  change ⁅Matrix.GeneralLinearGroup.elementaryUnit i j (ne_of_lt hij) a,
      Matrix.GeneralLinearGroup.elementaryUnit j k (ne_of_lt hjk) b⁆ =
    Matrix.GeneralLinearGroup.elementaryUnit i k (ne_of_lt (lt_trans hij hjk)) (a * b)
  exact Matrix.GeneralLinearGroup.elementaryUnit_commutator i j k
    (ne_of_lt hij) (ne_of_lt hjk) (ne_of_lt (lt_trans hij hjk)) a b

private theorem elementary_mem_lowerCentralSeries (k : ℕ)
    (hk : 1 ≤ k) (hkn : k < n) :
    elementary n R ⟨0, by omega⟩ ⟨k, hkn⟩ (by simp only [Fin.lt_def]; omega) 1 ∈
      (⊤ : Subgroup (Matrix.UnitriangularGroup (Fin n) R)).lowerCentralSeries (k - 1) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hzero : k = 0
    · subst k
      simp only [Nat.zero_add, Nat.reduceSubDiff,
        Subgroup.lowerCentralSeries_zero]
      exact Subgroup.mem_top _
    · have hk' : 1 ≤ k := by omega
      have hkn' : k < n := by omega
      have hfirst : (⟨0, by omega⟩ : Fin n) < ⟨k, hkn'⟩ := by
        simp only [Fin.lt_def]; omega
      have hnext : (⟨k, hkn'⟩ : Fin n) < ⟨k + 1, hkn⟩ := by
        simp only [Fin.lt_def]; omega
      have hmem := Subgroup.commutator_mem_commutator
        (ih hk' hkn')
        (Subgroup.mem_top (elementary n R ⟨k, hkn'⟩ ⟨k + 1, hkn⟩ hnext 1))
      have hroot := elementary_commutator n R ⟨0, by omega⟩ ⟨k, hkn'⟩
        ⟨k + 1, hkn⟩ hfirst hnext (1 : R) (1 : R)
      simpa only [Subgroup.lowerCentralSeries_succ, one_mul, hroot,
        show k + 1 - 1 = (k - 1) + 1 by omega] using hmem

private theorem elementary_ne_one [Nontrivial R] (k : ℕ)
    (hk : 1 ≤ k) (hkn : k < n) :
    elementary n R ⟨0, by omega⟩ ⟨k, hkn⟩ (by simp only [Fin.lt_def]; omega) (1 : R) ≠ 1 := by
  intro heq
  have hentry := congrArg (fun g : Matrix.UnitriangularGroup (Fin n) R =>
    ((g.1 : Matrix (Fin n) (Fin n) R) ⟨0, by omega⟩ ⟨k, hkn⟩)) heq
  have hzero : (⟨0, by omega⟩ : Fin n) ≠ ⟨k, hkn⟩ := by
    simp only [ne_eq, Fin.mk_eq_mk]; omega
  simp [elementary_coe, Matrix.add_apply, hzero] at hentry

/-- Over a nontrivial ring the upper bound is sharp in every finite dimension.
The proof uses the elementary commutator formalized in
`GeneralLinearGroups.ElementaryCommutator` and Mathlib's lower-central-series
class criterion. Milne, *Algebraic Groups* (2017), Example 6.36 and §6.49,
give field-based point-group nilpotence through the algebraic-group central
series, not this exact `n-1` point-group class. -/
theorem nilpotencyClass_eq_of_nontrivial [Nontrivial R] :
    Group.nilpotencyClass (Matrix.UnitriangularGroup (Fin n) R) = n - 1 := by
  have hupper := nilpotencyClass_le n R
  by_cases hsmall : n ≤ 1
  · exact le_antisymm hupper (by omega)
  · have hn : 2 ≤ n := by omega
    have hk : 1 ≤ n - 1 := by omega
    have hkn : n - 1 < n := by omega
    have hmem := elementary_mem_lowerCentralSeries n R (n - 1) hk hkn
    have hne := elementary_ne_one n R (n - 1) hk hkn
    have hnotbot :
        (⊤ : Subgroup (Matrix.UnitriangularGroup (Fin n) R)).lowerCentralSeries
          (n - 2) ≠ ⊥ := by
      intro hbot
      have hmem' : elementary n R ⟨0, by omega⟩ ⟨n - 1, hkn⟩
          (by simp only [Fin.lt_def]; omega) (1 : R) ∈
          (⊥ : Subgroup (Matrix.UnitriangularGroup (Fin n) R)) := by
        rw [← hbot]
        simpa only [show n - 1 - 1 = n - 2 by omega] using hmem
      exact hne (Subgroup.mem_bot.mp hmem')
    have hnot : ¬ Group.nilpotencyClass (Matrix.UnitriangularGroup (Fin n) R) ≤
        n - 2 := by
      intro hle
      exact hnotbot (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hle)
    omega

/-- Every unitriangular group over a subsingleton ring has nilpotency class
zero, using Mathlib's `Group.nilpotencyClass_zero_iff_subsingleton`. -/
theorem nilpotencyClass_eq_zero_of_subsingleton [Subsingleton R] :
    Group.nilpotencyClass (Matrix.UnitriangularGroup (Fin n) R) = 0 := by
  have hsub : Subsingleton (Matrix.UnitriangularGroup (Fin n) R) :=
    ⟨fun g h => by
      apply Subtype.ext
      apply Units.ext
      ext i j
      exact Subsingleton.elim _ _⟩
  exact Group.nilpotencyClass_zero_iff_subsingleton.mpr hsub

end Matrix.UnitriangularGroup
