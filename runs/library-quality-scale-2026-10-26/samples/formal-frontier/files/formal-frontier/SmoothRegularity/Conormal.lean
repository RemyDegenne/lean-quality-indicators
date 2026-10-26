/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Unramified.Basic

/-!
# Conormal modules with split residue field

This file studies the conormal module of a local algebra whose residue field
map splits as an algebra map.
-/

public section

open scoped TensorProduct

namespace IsLocalRing

universe u v

section

variable {K : Type u} {R : Type v} [Field K] [CommRing R] [IsLocalRing R]
  [Algebra K R]

private noncomputable def residueDifference
    (s : ResidueField R →ₐ[K] R)
    (hs : Function.LeftInverse (algebraMap R (ResidueField R)) s) (r : R) :
    maximalIdeal R :=
  ⟨r - s (residue R r), by
    rw [← residue_eq_zero_iff]
    simp only [map_sub, sub_eq_zero]
    rw [← ResidueField.algebraMap_eq]
    exact (hs _).symm⟩

private lemma residueDifference_add
    (s : ResidueField R →ₐ[K] R)
    (hs : Function.LeftInverse (algebraMap R (ResidueField R)) s) (x y : R) :
    residueDifference s hs (x + y) = residueDifference s hs x + residueDifference s hs y := by
  ext
  simp only [residueDifference, map_add, Submodule.coe_mk, Submodule.coe_add]
  ring

private lemma residueDifference_smul
    (s : ResidueField R →ₐ[K] R)
    (hs : Function.LeftInverse (algebraMap R (ResidueField R)) s) (k : K) (x : R) :
    residueDifference s hs (k • x) = k • residueDifference s hs x := by
  rw [← IsScalarTower.algebraMap_smul R k x,
    ← IsScalarTower.algebraMap_smul R k (residueDifference s hs x)]
  apply Subtype.ext
  dsimp only [residueDifference]
  change (algebraMap K R) k * x - s (residue R ((algebraMap K R) k * x)) =
    (algebraMap K R) k * (x - s (residue R x))
  have hk : residue R ((algebraMap K R) k) = algebraMap K (ResidueField R) k := by
    rw [← ResidueField.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply K R (ResidueField R)]
  rw [map_mul, hk, map_mul, s.commutes]
  ring

private noncomputable def splitResidueDerivation
    (s : ResidueField R →ₐ[K] R)
    (hs : Function.LeftInverse (algebraMap R (ResidueField R)) s) :
    Derivation K R (CotangentSpace R) where
  toLinearMap :=
    { toFun := fun r ↦ (maximalIdeal R).toCotangent (residueDifference s hs r)
      map_add' := fun x y ↦ by rw [residueDifference_add, map_add]
      map_smul' := fun k x ↦ by
        rw [residueDifference_smul]
        exact (maximalIdeal R).toCotangent.map_smul_of_tower k _ }
  map_one_eq_zero' := by
    change (maximalIdeal R).toCotangent (residueDifference s hs 1) = 0
    rw [show residueDifference s hs 1 = 0 by ext; simp [residueDifference], map_zero]
  leibniz' := fun x y ↦ by
    change (maximalIdeal R).toCotangent (residueDifference s hs (x * y)) =
      (maximalIdeal R).toCotangent (x • residueDifference s hs y) +
        (maximalIdeal R).toCotangent (y • residueDifference s hs x)
    rw [← map_add, ← sub_eq_zero, ← map_sub, Ideal.toCotangent_eq_zero]
    have hprod : -((residueDifference s hs x : R) * residueDifference s hs y) ∈
        maximalIdeal R ^ 2 := by
      apply (maximalIdeal R ^ 2).neg_mem
      rw [pow_two]
      exact Ideal.mul_mem_mul (residueDifference s hs x).2 (residueDifference s hs y).2
    convert hprod using 1
    change x * y - s (residue R (x * y)) -
        (x * (y - s (residue R y)) + y * (x - s (residue R x))) =
      -((x - s (residue R x)) * (y - s (residue R y)))
    simp only [map_mul]
    ring

private noncomputable def splitResidueRetraction
    (s : ResidueField R →ₐ[K] R)
    (hs : Function.LeftInverse (algebraMap R (ResidueField R)) s) :
    LinearMap (RingHom.id (ResidueField R)) (ResidueField R ⊗[R] Ω[R⁄K])
      (CotangentSpace R) :=
  (TensorProduct.isBaseChange R Ω[R⁄K] (ResidueField R)).lift
    (splitResidueDerivation s hs).liftKaehlerDifferential

private lemma splitResidueRetraction_comp
    (s : ResidueField R →ₐ[K] R)
    (hs : Function.LeftInverse (algebraMap R (ResidueField R)) s)
    (hker : RingHom.ker (algebraMap R (ResidueField R)) = maximalIdeal R) :
    (splitResidueRetraction s hs).restrictScalars R ∘ₗ
        KaehlerDifferential.kerCotangentToTensor K R (ResidueField R) =
      (Ideal.Cotangent.equivOfEq _ _ hker).toLinearMap := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ x
  rw [LinearMap.comp_apply, KaehlerDifferential.kerCotangentToTensor_toCotangent]
  change splitResidueRetraction s hs (1 ⊗ₜ[R] KaehlerDifferential.D K R x.1) = _
  rw [splitResidueRetraction, show (1 ⊗ₜ[R] KaehlerDifferential.D K R x.1) =
      (TensorProduct.mk R (ResidueField R) Ω[R⁄K] 1) (KaehlerDifferential.D K R x.1) by rfl,
    IsBaseChange.lift_eq, Derivation.liftKaehlerDifferential_comp_D]
  change (maximalIdeal R).toCotangent (residueDifference s hs x.1) =
    Ideal.Cotangent.equivOfEq _ _ hker
      ((RingHom.ker (algebraMap R (ResidueField R))).toCotangent x)
  rw [Ideal.Cotangent.equivOfEq_toCotangent]
  apply (maximalIdeal R).toCotangent.congr_arg
  ext
  simp only [residueDifference]
  have hx : residue R x.1 = 0 := by
    rw [← ResidueField.algebraMap_eq]
    exact RingHom.mem_ker.mp x.2
  rw [hx, map_zero, sub_zero]
  rfl

/--
If the residue map of a local `K`-algebra has a `K`-algebra section and the
residue field is formally unramified over `K`, its cotangent space is the base
change of its module of Kähler differentials to the residue field.
-/
noncomputable def cotangentSpaceEquivTensorKaehlerOfSection
    [Algebra.FormallyUnramified K (ResidueField R)]
    (s : ResidueField R →ₐ[K] R)
    (hs : Function.LeftInverse (algebraMap R (ResidueField R)) s) :
    LinearEquiv (RingHom.id (ResidueField R)) (CotangentSpace R)
      (ResidueField R ⊗[R] Ω[R⁄K]) := by
  let hker : RingHom.ker (algebraMap R (ResidueField R)) = maximalIdeal R := by
    rw [ResidueField.algebraMap_eq, ker_residue]
  let f := KaehlerDifferential.kerCotangentToTensor K R (ResidueField R)
  have hf_injective : Function.Injective f := by
    intro x y hxy
    apply (Ideal.Cotangent.equivOfEq _ _ hker).injective
    have hcomp := splitResidueRetraction_comp s hs hker
    exact (LinearMap.congr_fun hcomp x).symm.trans <|
      (congr_arg (splitResidueRetraction s hs) hxy).trans (LinearMap.congr_fun hcomp y)
  have hf_surjective : Function.Surjective f := by
    rw [← LinearMap.range_eq_top,
      KaehlerDifferential.range_kerCotangentToTensor K R (ResidueField R) residue_surjective]
    ext x
    simp only [Submodule.restrictScalars_mem, LinearMap.mem_ker, Submodule.mem_top, iff_true]
    exact Subsingleton.elim _ _
  exact LinearEquiv.extendScalarsOfSurjective residue_surjective <|
    (Ideal.Cotangent.equivOfEq _ _ hker).symm.trans
      (LinearEquiv.ofBijective f ⟨hf_injective, hf_surjective⟩)

/-- The split-residue cotangent equivalence sends a class in the maximal ideal to
the corresponding differential in the residue-field base change. -/
theorem cotangentSpaceEquivTensorKaehlerOfSection_apply_toCotangent
    [Algebra.FormallyUnramified K (ResidueField R)]
    (s : ResidueField R →ₐ[K] R)
    (hs : Function.LeftInverse (algebraMap R (ResidueField R)) s)
    (x : maximalIdeal R) :
    cotangentSpaceEquivTensorKaehlerOfSection s hs
        ((maximalIdeal R).toCotangent x) =
      1 ⊗ₜ[R] KaehlerDifferential.D K R x.1 := by
  rfl

private noncomputable def residueSection
    (e : ResidueField R ≃ₐ[K] K) : ResidueField R →ₐ[K] R :=
  (Algebra.ofId K R).comp e.toAlgHom

private lemma residueSection_isSection (e : ResidueField R ≃ₐ[K] K) :
    Function.LeftInverse (algebraMap R (ResidueField R)) (residueSection e) := by
  intro x
  change algebraMap R (ResidueField R) ((algebraMap K R) (e x)) = x
  rw [← IsScalarTower.algebraMap_apply K R (ResidueField R)]
  apply e.injective
  simp

/--
If a local `K`-algebra has residue field isomorphic to `K` as a `K`-algebra,
its cotangent space is the base change of its module of Kähler differentials to
the residue field.
-/
noncomputable def cotangentSpaceEquivTensorKaehlerOfResidueEquiv
    (e : ResidueField R ≃ₐ[K] K) :
    LinearEquiv (RingHom.id (ResidueField R)) (CotangentSpace R)
      (ResidueField R ⊗[R] Ω[R⁄K]) := by
  letI : Algebra.FormallyUnramified K (ResidueField R) :=
    Algebra.FormallyUnramified.of_equiv e.symm
  exact cotangentSpaceEquivTensorKaehlerOfSection (residueSection e)
    (residueSection_isSection e)

/-- The cotangent equivalence induced by a residue-field equivalence sends a
class in the maximal ideal to its differential in the base change. -/
theorem cotangentSpaceEquivTensorKaehlerOfResidueEquiv_apply_toCotangent
    (e : ResidueField R ≃ₐ[K] K) (x : maximalIdeal R) :
    cotangentSpaceEquivTensorKaehlerOfResidueEquiv e
        ((maximalIdeal R).toCotangent x) =
      1 ⊗ₜ[R] KaehlerDifferential.D K R x.1 := by
  rfl

end

end IsLocalRing
