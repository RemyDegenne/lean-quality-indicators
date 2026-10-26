/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.Whitehead
public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.TwoSidedIdeal.Instances
public import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# General linear congruence subgroups

This file defines the general linear group of a nonunital two-sided ideal by
unitization and identifies it canonically with the kernel of reduction modulo
that ideal.  The resulting map into the ambient general linear group is
injective and exact at the ambient group for every two-sided ideal.

Surjectivity of reduction is a separate property of the ideal; for
quasi-regular ideals it is supplied by `mapRingHom_quotient_surjective`.
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v

variable {R : Type u} [Ring R]
variable {n : Type v} [Fintype n] [DecidableEq n]

/-- Inclusion of a two-sided ideal as a nonunital algebra map over `ℤ`. -/
def idealInclusion (I : TwoSidedIdeal R) : I →ₙₐ[ℤ] R where
  toFun x := x.1
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl

/-- The canonical map from the unitization of an ideal to its ambient ring,
`(z, i) ↦ z + i`. -/
def idealUnitizationToRing (I : TwoSidedIdeal R) : Unitization ℤ I →+* R :=
  (idealInclusion I).toAlgHom.toRingHom

/-- The ambient-ring map adds the integer part and the ideal part of a unitized coefficient. -/
@[simp]
theorem idealUnitizationToRing_apply (I : TwoSidedIdeal R)
    (z : Unitization ℤ I) :
    idealUnitizationToRing I z = (z.fst : R) + z.snd.1 := rfl

/-- The augmentation from the general linear group of an ideal's unitization
to the general linear group over `ℤ`. -/
def idealAugmentation (I : TwoSidedIdeal R) :
    GL n (Unitization ℤ I) →* GL n ℤ :=
  mapRingHom (Unitization.fstHom (R := ℤ) (A := I)).toRingHom

/-- The general linear group of a nonunital two-sided ideal, defined as the
kernel of the augmentation on its unitization. -/
def idealGeneralLinearGroup (I : TwoSidedIdeal R) :
    Subgroup (GL n (Unitization ℤ I)) :=
  MonoidHom.ker (idealAugmentation (n := n) I)

/-- The congruence subgroup attached to a two-sided ideal: the kernel of
entrywise reduction modulo that ideal. -/
def congruenceSubgroup (I : TwoSidedIdeal R) : Subgroup (GL n R) :=
  MonoidHom.ker (mapRingHom (Ideal.Quotient.mk I.asIdeal) :
    GL n R →* GL n (R ⧸ I.asIdeal))

/-- The map from the unitized general linear group to the ambient general
linear group. -/
def idealUnitizationMap (I : TwoSidedIdeal R) :
    GL n (Unitization ℤ I) →* GL n R :=
  mapRingHom (idealUnitizationToRing I)

/-- An element of the ideal has zero image in the ambient quotient ring. -/
@[simp]
theorem quotient_mk_ideal_coe_eq_zero (I : TwoSidedIdeal R) (x : I) :
    Ideal.Quotient.mk I.asIdeal (x : R) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact TwoSidedIdeal.mem_asIdeal.mpr x.property

/-- An augmentation-kernel unit maps to an ambient unit congruent to the identity modulo `I`. -/
theorem idealGeneralLinearGroup_map_mem_congruenceSubgroup
    (I : TwoSidedIdeal R) (u : idealGeneralLinearGroup (n := n) I) :
    idealUnitizationMap (n := n) I u.1 ∈ congruenceSubgroup (n := n) I := by
  change mapRingHom (Ideal.Quotient.mk I.asIdeal)
      (idealUnitizationMap (n := n) I u.1) = 1
  apply Units.ext
  ext i j
  have hu := congrArg
    (fun g : GL n ℤ => (g : Matrix n n ℤ) i j) u.2
  change Ideal.Quotient.mk I.asIdeal
      (idealUnitizationToRing I ((u.1 : GL n (Unitization ℤ I)) i j)) =
    (1 : Matrix n n (R ⧸ I.asIdeal)) i j
  rw [idealUnitizationToRing_apply, map_add,
    quotient_mk_ideal_coe_eq_zero, add_zero]
  change (((u.1 : GL n (Unitization ℤ I)) i j).fst :
      R ⧸ I.asIdeal) = _
  change ((u.1 : GL n (Unitization ℤ I)) i j).fst =
    (1 : Matrix n n ℤ) i j at hu
  rw [hu]
  simp [Matrix.one_apply]

/-- The canonical homomorphism from the general linear group of an ideal to
the corresponding ambient congruence subgroup. -/
def idealGeneralLinearGroupToCongruence (I : TwoSidedIdeal R) :
    idealGeneralLinearGroup (n := n) I →* congruenceSubgroup (n := n) I where
  toFun u := ⟨idealUnitizationMap (n := n) I u.1,
    idealGeneralLinearGroup_map_mem_congruenceSubgroup I u⟩
  map_one' := by
    apply Subtype.ext
    exact (idealUnitizationMap (n := n) I).map_one
  map_mul' x y := by
    apply Subtype.ext
    exact (idealUnitizationMap (n := n) I).map_mul x.1 y.1

/-- The integer component of each entry of an augmentation-kernel unit is the identity entry. -/
theorem idealGeneralLinearGroup_entry_fst
    (I : TwoSidedIdeal R) (u : idealGeneralLinearGroup (n := n) I)
    (i j : n) :
    ((u.1 : GL n (Unitization ℤ I)) i j).fst =
      (1 : Matrix n n ℤ) i j := by
  have hu := congrArg
    (fun g : GL n ℤ => (g : Matrix n n ℤ) i j) u.2
  exact hu

/-- Each entry of a congruence-subgroup unit differs from the identity entry
by an element of `I`. -/
theorem congruenceSubgroup_entry_sub_mem
    (I : TwoSidedIdeal R) (u : congruenceSubgroup (n := n) I)
    (i j : n) :
    (u.1 : Matrix n n R) i j - (1 : Matrix n n R) i j ∈ I := by
  apply TwoSidedIdeal.mem_asIdeal.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub]
  apply sub_eq_zero.mpr
  have hu := congrArg
    (fun g : GL n (R ⧸ I.asIdeal) =>
      (g : Matrix n n (R ⧸ I.asIdeal)) i j) u.2
  change Ideal.Quotient.mk I.asIdeal ((u.1 : Matrix n n R) i j) =
    (1 : Matrix n n (R ⧸ I.asIdeal)) i j at hu
  simpa [Matrix.one_apply] using hu

/-- The canonical coefficient lift of an ambient matrix congruent to the
identity modulo `I`. -/
def liftCongruenceEntry (I : TwoSidedIdeal R)
    (u : congruenceSubgroup (n := n) I) (i j : n) :
    Unitization ℤ I :=
  Unitization.mk
    ((1 : Matrix n n ℤ) i j,
      ⟨(u.1 : Matrix n n R) i j - (1 : Matrix n n R) i j,
        congruenceSubgroup_entry_sub_mem I u i j⟩)

/-- Lift a congruence-subgroup matrix entrywise to `Unitization ℤ I`, with integer part the
identity matrix and ideal part its difference from the identity. -/
def liftCongruenceMatrix (I : TwoSidedIdeal R)
    (u : congruenceSubgroup (n := n) I) :
    Matrix n n (Unitization ℤ I) :=
  fun i j => liftCongruenceEntry I u i j

/-- The integer component of a lifted entry is the corresponding identity-matrix entry. -/
@[simp]
theorem liftCongruenceEntry_fst (I : TwoSidedIdeal R)
    (u : congruenceSubgroup (n := n) I) (i j : n) :
    (liftCongruenceEntry I u i j).fst =
      (1 : Matrix n n ℤ) i j := rfl

/-- Mapping a lifted coefficient back to the ambient ring recovers the original entry. -/
@[simp]
theorem idealUnitizationToRing_liftCongruenceEntry
    (I : TwoSidedIdeal R) (u : congruenceSubgroup (n := n) I)
    (i j : n) :
    idealUnitizationToRing I (liftCongruenceEntry I u i j) =
      (u.1 : Matrix n n R) i j := by
  simp only [liftCongruenceEntry, idealUnitizationToRing_apply]
  simp [Matrix.one_apply]

/-- Entrywise augmentation of a lifted congruence matrix is the identity matrix over `ℤ`. -/
theorem fstHom_map_liftCongruenceMatrix (I : TwoSidedIdeal R)
    (u : congruenceSubgroup (n := n) I) :
    (Unitization.fstHom (R := ℤ) (A := I)).toRingHom.mapMatrix
        (liftCongruenceMatrix I u) = 1 := by
  ext i j
  simp [liftCongruenceMatrix]

/-- The ambient-ring image of a lifted congruence matrix is the original matrix. -/
theorem idealUnitizationToRing_map_liftCongruenceMatrix
    (I : TwoSidedIdeal R) (u : congruenceSubgroup (n := n) I) :
    (idealUnitizationToRing I).mapMatrix (liftCongruenceMatrix I u) =
      (u.1 : Matrix n n R) := by
  ext i j
  exact idealUnitizationToRing_liftCongruenceEntry I u i j

/-- A unitized ideal coefficient is determined by its integer component and ambient-ring image. -/
theorem unitization_eq_of_fst_eq_of_idealUnitizationToRing_eq
    (I : TwoSidedIdeal R) {x y : Unitization ℤ I}
    (hfst : x.fst = y.fst)
    (hmap : idealUnitizationToRing I x = idealUnitizationToRing I y) :
    x = y := by
  apply Unitization.ext hfst
  rw [idealUnitizationToRing_apply, idealUnitizationToRing_apply, hfst] at hmap
  exact Subtype.ext (add_left_cancel hmap)

/-- Matrices over an ideal's unitization are determined by their augmentation and ambient image. -/
theorem unitizationMatrix_eq_of_fst_eq_of_idealUnitizationToRing_eq
    (I : TwoSidedIdeal R) {x y : Matrix n n (Unitization ℤ I)}
    (hfst :
      (Unitization.fstHom (R := ℤ) (A := I)).toRingHom.mapMatrix x =
        (Unitization.fstHom (R := ℤ) (A := I)).toRingHom.mapMatrix y)
    (hmap : (idealUnitizationToRing I).mapMatrix x =
      (idealUnitizationToRing I).mapMatrix y) : x = y := by
  apply Matrix.ext
  intro i j
  apply unitization_eq_of_fst_eq_of_idealUnitizationToRing_eq I
  · exact congrArg (fun m => m i j) hfst
  · exact congrArg (fun m => m i j) hmap

/-- An ambient unit congruent to the identity and its inverse lift to mutually
inverse matrices over the ideal's unitization. -/
def liftCongruenceUnit (I : TwoSidedIdeal R)
    (u : congruenceSubgroup (n := n) I) :
    GL n (Unitization ℤ I) where
  val := liftCongruenceMatrix I u
  inv := liftCongruenceMatrix I u⁻¹
  val_inv := by
    apply unitizationMatrix_eq_of_fst_eq_of_idealUnitizationToRing_eq I
    · rw [map_mul, fstHom_map_liftCongruenceMatrix,
        fstHom_map_liftCongruenceMatrix, mul_one, map_one]
    · rw [map_mul, idealUnitizationToRing_map_liftCongruenceMatrix,
        idealUnitizationToRing_map_liftCongruenceMatrix, map_one]
      change (u.1 : Matrix n n R) * u.1.inv = 1
      exact u.1.val_inv
  inv_val := by
    apply unitizationMatrix_eq_of_fst_eq_of_idealUnitizationToRing_eq I
    · rw [map_mul, fstHom_map_liftCongruenceMatrix,
        fstHom_map_liftCongruenceMatrix, mul_one, map_one]
    · rw [map_mul, idealUnitizationToRing_map_liftCongruenceMatrix,
        idealUnitizationToRing_map_liftCongruenceMatrix, map_one]
      change u.1.inv * (u.1 : Matrix n n R) = 1
      exact u.1.inv_val

/-- Lift an ambient congruence-subgroup unit into the augmentation kernel over `Unitization ℤ I`,
using the lifted original matrix and the lifted inverse matrix as its unit data. -/
def congruenceSubgroupToIdealGeneralLinearGroup
    (I : TwoSidedIdeal R) (u : congruenceSubgroup (n := n) I) :
    idealGeneralLinearGroup (n := n) I := by
  refine ⟨liftCongruenceUnit I u, ?_⟩
  apply Units.ext
  exact fstHom_map_liftCongruenceMatrix I u

/-- Mapping the unitized lift of a congruence-subgroup element back recovers that element. -/
theorem idealGeneralLinearGroupToCongruence_rightInverse
    (I : TwoSidedIdeal R) (u : congruenceSubgroup (n := n) I) :
    idealGeneralLinearGroupToCongruence (n := n) I
      (congruenceSubgroupToIdealGeneralLinearGroup I u) = u := by
  apply Subtype.ext
  apply Units.ext
  exact idealUnitizationToRing_map_liftCongruenceMatrix I u

/-- The map from the ideal's augmentation-kernel group to the ambient congruence subgroup
is injective. -/
theorem idealGeneralLinearGroupToCongruence_injective
    (I : TwoSidedIdeal R) :
    Function.Injective (idealGeneralLinearGroupToCongruence (n := n) I) := by
  intro x y hxy
  apply Subtype.ext
  apply Units.ext
  apply unitizationMatrix_eq_of_fst_eq_of_idealUnitizationToRing_eq I
  · ext i j
    exact (idealGeneralLinearGroup_entry_fst I x i j).trans
      (idealGeneralLinearGroup_entry_fst I y i j).symm
  · have h := congrArg
      (fun z : congruenceSubgroup (n := n) I =>
        (z.1 : Matrix n n R)) hxy
    exact h

/-- The unitization construction maps bijectively onto the ambient congruence subgroup. -/
theorem idealGeneralLinearGroupToCongruence_bijective
    (I : TwoSidedIdeal R) :
    Function.Bijective (idealGeneralLinearGroupToCongruence (n := n) I) :=
  ⟨idealGeneralLinearGroupToCongruence_injective I,
    fun u => ⟨congruenceSubgroupToIdealGeneralLinearGroup I u,
      idealGeneralLinearGroupToCongruence_rightInverse I u⟩⟩

/-- The general linear group of a two-sided ideal is canonically equivalent to
the corresponding ambient congruence subgroup. -/
noncomputable def idealGeneralLinearGroupEquivCongruence
    (I : TwoSidedIdeal R) :
    idealGeneralLinearGroup (n := n) I ≃*
      congruenceSubgroup (n := n) I :=
  MulEquiv.ofBijective (idealGeneralLinearGroupToCongruence (n := n) I)
    (idealGeneralLinearGroupToCongruence_bijective I)

/-- The inclusion of the general linear group of an ideal into the ambient
general linear group. -/
def idealGeneralLinearGroupToRing (I : TwoSidedIdeal R) :
    idealGeneralLinearGroup (n := n) I →* GL n R :=
  (congruenceSubgroup (n := n) I).subtype.comp
    (idealGeneralLinearGroupToCongruence (n := n) I)

/-- The homomorphism from the ideal's general linear group to the ambient group is injective. -/
theorem idealGeneralLinearGroupToRing_injective (I : TwoSidedIdeal R) :
    Function.Injective (idealGeneralLinearGroupToRing (n := n) I) := by
  intro x y hxy
  apply idealGeneralLinearGroupToCongruence_injective I
  apply Subtype.ext
  exact hxy

/-- For every two-sided ideal, its general linear group maps exactly onto the
kernel of reduction from the ambient general linear group. -/
theorem idealGeneralLinearGroupToRing_mulExact (I : TwoSidedIdeal R) :
    Function.MulExact (idealGeneralLinearGroupToRing (n := n) I)
      (mapRingHom (Ideal.Quotient.mk I.asIdeal) :
        GL n R →* GL n (R ⧸ I.asIdeal)) := by
  apply MonoidHom.mulExact_iff.mpr
  apply le_antisymm
  · intro x hx
    let u : congruenceSubgroup (n := n) I := ⟨x, hx⟩
    obtain ⟨y, hy⟩ :=
      (idealGeneralLinearGroupToCongruence_bijective I).2 u
    apply MonoidHom.mem_range.mpr
    refine ⟨y, ?_⟩
    exact congrArg Subtype.val hy
  · intro x hx
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx
    exact (idealGeneralLinearGroupToCongruence (n := n) I y).property

end Matrix.GeneralLinearGroup
