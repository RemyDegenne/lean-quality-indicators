/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.GeneralSpecialLinearSmooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.Algebra.Ring.Hom.InjSurj

/-!
# Integral finite general and special linear schemes

The genuine coordinate algebras of finite `GL` and `SL` are domains over integral
base rings. Over any commutative base their structure maps have integral fibers
after extension to every field, so both morphisms are geometrically integral.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.8 for the field-base determinant
  localization of `GL`, and §2.42 for the field-base domain argument for `SL`.
  The assertions here also concern integral-base coordinate rings and
  relative geometric integrality over arbitrary bases.
* J. S. Milne, *Basic Theory of Affine Group Schemes* (2012), XIII §3,
  item 3.14: a right-diagonal determinant splitting for positive rank.
  The algebra section used here instead comes from left normalization; it is
  not an assertion that arbitrary injections survive tensor products.
* Mathlib, `RingTheory/Localization/Away/Basic`,
  `RingTheory/Localization/BaseChange`, `RingTheory/TensorProduct/MvPolynomial`,
  `AlgebraicGeometry/Geometrically/Integral` and
  `AlgebraicGeometry/Pullbacks`: localization domains, tensor equivalences,
  geometric-fiber criteria and affine pullbacks. Compatibility of the generic
  determinant with coefficient maps is checked explicitly below.
-/

@[expose] public section

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits
open GeneralLinearCoordinateRing SpecialLinearCoordinateRing
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- The actual determinant-localized finite general linear coordinate ring is a domain
over an integral domain, including for an empty index. This extends the
field-base `GL` determinant localization in Milne, *Algebraic Groups*, §2.8, using
mathlib's domain theorem for localization away from a nonzero element. -/
instance generalLinearCoordinateRing_isDomain [IsDomain K] :
    IsDomain (GeneralLinearCoordinateRing.CoordinateRing K n) :=
  Localization.Away.isDomain (Matrix.det_mvPolynomialX_ne_zero n K)

private def emptySpecialLinearEquiv [IsEmpty n] :
    GeneralLinearCoordinateRing.CoordinateRing K n ≃ₐ[K]
      SpecialLinearCoordinateRing.CoordinateRing K n := by
  have determinant_one : (matrix K n).det = 1 := Matrix.det_isEmpty
  have ideal_bot : SpecialLinearCoordinateRing.determinantOneIdeal K n = ⊥ := by
    simp [SpecialLinearCoordinateRing.determinantOneIdeal, determinant_one]
  exact (AlgEquiv.quotientBot K (GeneralLinearCoordinateRing.CoordinateRing K n)).symm.trans
    (Ideal.quotientEquivAlgOfEq K ideal_bot.symm)

private theorem emptySpecialLinearEquiv_quotient [IsEmpty n] :
    (emptySpecialLinearEquiv K n).toAlgHom = SpecialLinearCoordinateRing.quotient K n := by
  ext x
  rfl

private def specialLinearSection :
    SpecialLinearCoordinateRing.CoordinateRing K n →ₐ[K]
      GeneralLinearCoordinateRing.CoordinateRing K n := by
  classical
  exact if nonemptyIndex : Nonempty n then
    specialLinearNormalizationSection K n (Classical.choice nonemptyIndex)
  else
    letI : IsEmpty n := ⟨fun index => nonemptyIndex ⟨index⟩⟩
    (emptySpecialLinearEquiv K n).symm.toAlgHom

private theorem specialLinearSection_split :
    (SpecialLinearCoordinateRing.quotient K n).comp (specialLinearSection K n) =
      AlgHom.id K (SpecialLinearCoordinateRing.CoordinateRing K n) := by
  classical
  unfold specialLinearSection
  split_ifs with nonemptyIndex
  · exact specialLinearNormalizationSection_comp_quotient K n _
  · let : IsEmpty n := ⟨fun index => nonemptyIndex ⟨index⟩⟩
    rw [← emptySpecialLinearEquiv_quotient K n]
    exact AlgEquiv.comp_symm (emptySpecialLinearEquiv K n)

/-- The actual determinant-one coordinate ring is a domain over every integral base,
including in rank zero. Compare the positive-rank field-base result in Milne,
*Algebraic Groups*, §2.42: here the algebra section into the GL domain is
injective, while rank zero uses the quotient-bottom equivalence. -/
instance specialLinearCoordinateRing_isDomain [IsDomain K] :
    IsDomain (SpecialLinearCoordinateRing.CoordinateRing K n) := by
  have injective : Function.Injective (specialLinearSection K n) := by
    intro x y h
    have applied := congrArg (SpecialLinearCoordinateRing.quotient K n) h
    simpa only [← AlgHom.comp_apply, specialLinearSection_split, AlgHom.id_apply] using applied
  exact injective.isDomain (specialLinearSection K n)

/-- The total space of finite `GL` is integral over any integral base, using
mathlib's integral-affine-Spec instance for the GL coordinate domain. -/
instance generalLinearGroupUnderlyingScheme_isIntegral [IsDomain K] :
    IsIntegral (generalLinearGroupUnderlyingScheme K n).left := by
  change IsIntegral (Spec (.of (GeneralLinearCoordinateRing.CoordinateRing K n)))
  infer_instance

/-- The total space of finite `SL` is integral over any integral base, using
mathlib's integral-affine-Spec instance for the SL coordinate domain. -/
instance specialLinearGroupUnderlyingScheme_isIntegral [IsDomain K] :
    IsIntegral (specialLinearGroupUnderlyingScheme K n).left := by
  change IsIntegral (Spec (.of (SpecialLinearCoordinateRing.CoordinateRing K n)))
  infer_instance

private theorem determinant_map (F : Type u) [CommRing F] [Algebra K F] :
    MvPolynomial.map (algebraMap K F) (GeneralLinearCoordinateRing.determinant K n) =
      GeneralLinearCoordinateRing.determinant F n := by
  unfold GeneralLinearCoordinateRing.determinant
  have mappedMatrix :
      (MvPolynomial.map (algebraMap K F)).mapMatrix (Matrix.mvPolynomialX n n K) =
        Matrix.mvPolynomialX n n F := by
    ext i j
    simp [Matrix.mvPolynomialX]
  rw [RingHom.map_det, mappedMatrix]

private theorem generalLinearTensor_isDomain (F : Type u) [Field F] [Algebra K F] :
    IsDomain (F ⊗[K] GeneralLinearCoordinateRing.CoordinateRing K n) := by
  let polynomialEquiv := MvPolynomial.algebraTensorAlgEquiv (σ := n × n) K F
  have : IsDomain (F ⊗[K] GeneralLinearCoordinateRing.PolynomialRing K n) :=
    polynomialEquiv.injective.isDomain polynomialEquiv.toRingHom
  have determinant_ne : (1 : F) ⊗ₜ[K] GeneralLinearCoordinateRing.determinant K n ≠ 0 := by
    intro equalZero
    have mapped := congrArg polynomialEquiv equalZero
    have mappedDet : polynomialEquiv
        ((1 : F) ⊗ₜ[K] GeneralLinearCoordinateRing.determinant K n) =
        GeneralLinearCoordinateRing.determinant F n := by
      simp only [polynomialEquiv, MvPolynomial.algebraTensorAlgEquiv_tmul,
        one_smul, determinant_map K n F]
    rw [mappedDet, map_zero] at mapped
    exact (Matrix.det_mvPolynomialX_ne_zero n F) mapped
  have : IsDomain (Localization.Away
      ((1 : F) ⊗ₜ[K] GeneralLinearCoordinateRing.determinant K n)) :=
    Localization.Away.isDomain determinant_ne
  let localizationEquiv := IsLocalization.Away.tensorProductEquivTMulRight K F
    (GeneralLinearCoordinateRing.determinant K n)
    (GeneralLinearCoordinateRing.CoordinateRing K n)
  exact localizationEquiv.injective.isDomain localizationEquiv.toRingHom

private theorem specialLinearTensor_isDomain (F : Type u) [Field F] [Algebra K F] :
    IsDomain (F ⊗[K] SpecialLinearCoordinateRing.CoordinateRing K n) := by
  have : IsDomain (F ⊗[K] GeneralLinearCoordinateRing.CoordinateRing K n) :=
    generalLinearTensor_isDomain K n F
  let quotientTensor :
      F ⊗[K] GeneralLinearCoordinateRing.CoordinateRing K n →ₐ[F]
        F ⊗[K] SpecialLinearCoordinateRing.CoordinateRing K n :=
    Algebra.TensorProduct.map (AlgHom.id F F) (SpecialLinearCoordinateRing.quotient K n)
  let sectionTensor :
      F ⊗[K] SpecialLinearCoordinateRing.CoordinateRing K n →ₐ[F]
        F ⊗[K] GeneralLinearCoordinateRing.CoordinateRing K n :=
    Algebra.TensorProduct.map (AlgHom.id F F) (specialLinearSection K n)
  have split : quotientTensor.comp sectionTensor =
      AlgHom.id F (F ⊗[K] SpecialLinearCoordinateRing.CoordinateRing K n) := by
    dsimp [quotientTensor, sectionTensor]
    rw [← Algebra.TensorProduct.map_id_comp, specialLinearSection_split,
      Algebra.TensorProduct.map_id]
  have injective : Function.Injective sectionTensor := by
    intro x y h
    have applied := congrArg quotientTensor h
    simpa only [← AlgHom.comp_apply, split, AlgHom.id_apply] using applied
  exact injective.isDomain sectionTensor.toRingHom

private theorem integral_closedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme) IsIntegral := by
  constructor
  intro X Y iso integral
  let : IsIntegral X := integral
  exact IsIntegral.of_isIso iso.hom

/-- Every geometric fiber of the genuine finite general linear structure morphism
is integral, for every finite index and every commutative base. The field
presentation follows Milne, *Algebraic Groups*, §2.8; the relative proof uses
mathlib's polynomial-tensor and localization equivalences, geometric-fiber
criterion and affine-Spec pullback isomorphism. -/
instance generalLinearGroupUnderlyingScheme_geometricallyIntegral :
    GeometricallyIntegral (generalLinearGroupUnderlyingScheme K n).hom := by
  let : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme) IsIntegral :=
    integral_closedUnderIsomorphisms
  refine ⟨(geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := IsIntegral)).2 ?_⟩
  intro F _ _
  change IsIntegral (pullback
    (Spec.map (CommRingCat.ofHom
      (algebraMap K (GeneralLinearCoordinateRing.CoordinateRing K n))))
    (Spec.map (CommRingCat.ofHom (algebraMap K F))))
  have : IsDomain (F ⊗[K] GeneralLinearCoordinateRing.CoordinateRing K n) :=
    generalLinearTensor_isDomain K n F
  have : IsDomain
      (GeneralLinearCoordinateRing.CoordinateRing K n ⊗[K] F) :=
    (Algebra.TensorProduct.comm K
      (GeneralLinearCoordinateRing.CoordinateRing K n) F).injective.isDomain
        (Algebra.TensorProduct.comm K
          (GeneralLinearCoordinateRing.CoordinateRing K n) F).toRingHom
  exact IsIntegral.of_isIso
    (pullbackSpecIso K (GeneralLinearCoordinateRing.CoordinateRing K n) F).inv

/-- Every geometric fiber of the genuine finite special linear structure morphism
is integral, for every finite index and every commutative base. The field
case extends Milne, *Algebraic Groups*, §2.42; the relative proof tensors
the explicit algebra-section identity and uses mathlib's geometric-fiber
criterion and affine-Spec pullback isomorphism. -/
instance specialLinearGroupUnderlyingScheme_geometricallyIntegral :
    GeometricallyIntegral (specialLinearGroupUnderlyingScheme K n).hom := by
  let : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme) IsIntegral :=
    integral_closedUnderIsomorphisms
  refine ⟨(geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := IsIntegral)).2 ?_⟩
  intro F _ _
  change IsIntegral (pullback
    (Spec.map (CommRingCat.ofHom
      (algebraMap K (SpecialLinearCoordinateRing.CoordinateRing K n))))
    (Spec.map (CommRingCat.ofHom (algebraMap K F))))
  have : IsDomain (F ⊗[K] SpecialLinearCoordinateRing.CoordinateRing K n) :=
    specialLinearTensor_isDomain K n F
  have : IsDomain
      (SpecialLinearCoordinateRing.CoordinateRing K n ⊗[K] F) :=
    (Algebra.TensorProduct.comm K
      (SpecialLinearCoordinateRing.CoordinateRing K n) F).injective.isDomain
        (Algebra.TensorProduct.comm K
          (SpecialLinearCoordinateRing.CoordinateRing K n) F).toRingHom
  exact IsIntegral.of_isIso
    (pullbackSpecIso K (SpecialLinearCoordinateRing.CoordinateRing K n) F).inv

end AlgebraicGeometry
