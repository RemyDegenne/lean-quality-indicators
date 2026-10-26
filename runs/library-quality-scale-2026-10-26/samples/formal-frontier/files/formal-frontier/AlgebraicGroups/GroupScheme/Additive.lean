/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.SymmetricAlgebra
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.FiniteType

/-!
# The additive group scheme

This file packages the affine group scheme over an arbitrary commutative base
represented by the symmetric algebra on a free module of rank one. Its affine
points are naturally the additive groups of the test algebras, expressed through
`Multiplicative` so that they are objects of `GrpCat`. The distinguished coordinate
is primitive, has zero counit, and is negated by the antipode.

## Main definitions

- `AlgebraicGeometry.additiveGroupScheme`
- `AlgebraicGeometry.additiveGroupMulEquivAlgHom`
- `AlgebraicGeometry.additiveGroupMulEquivPoints`
- `AlgebraicGeometry.additiveGroupPointsIso`
- `AlgebraicGeometry.additiveGroupCoordinateAlgEquiv`

Milne's item 2.1 describes the field-base additive group by `k[T]`, its
algebra-valued points and the primitive coproduct of `T`. The rank-one
symmetric-algebra presentation here extends the base to any commutative ring;
its identification with `Polynomial K` uses Mathlib's basis equivalence and
does not assert a separate polynomial Hopf-algebra equivalence.

## References

- J. S. Milne, *Algebraic Groups* (2017), item 2.1 (additive group and
  coordinate coproduct).
- Mathlib, `Mathlib.RingTheory.Bialgebra.SymmetricAlgebra`,
  `Mathlib.LinearAlgebra.SymmetricAlgebra.Basis` (polynomial coordinates),
  `Mathlib.Algebra.MvPolynomial.Equiv` (one variable), and
  `Mathlib.Algebra.WithConv` (`WithConv.equiv`),
  `Mathlib.RingTheory.Bialgebra.Convolution` (`AlgHom.convMul_apply`), and
  `Mathlib.AlgebraicGeometry.Group.Affine` (`Spec.mapMulEquiv` and affine points).
-/

public section

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

/-- The rank-one symmetric-algebra coordinate ring of the additive group. -/
abbrev additiveGroupCoordinateRing
    (K : Type u) [CommRing K] := SymmetricAlgebra K K

/-- The universal primitive coordinate of the additive group. -/
@[expose] def additiveGroupCoordinate
    (K : Type u) [CommRing K] : additiveGroupCoordinateRing K :=
  SymmetricAlgebra.ι K K 1

/-- The standard polynomial presentation of the additive-group coordinate ring. -/
@[expose] def additiveGroupCoordinateAlgEquiv
  (K : Type u) [CommRing K] :
    additiveGroupCoordinateRing K ≃ₐ[K] Polynomial K :=
  (SymmetricAlgebra.equivMvPolynomial (Module.Basis.singleton Unit K)).trans
    (MvPolynomial.uniqueAlgEquiv K Unit)

/-- The universal coordinate is sent to `Polynomial.X` by the standard polynomial
presentation. -/
@[simp]
theorem additiveGroupCoordinateAlgEquiv_coordinate
    (K : Type u) [CommRing K] :
    additiveGroupCoordinateAlgEquiv K (additiveGroupCoordinate K) = Polynomial.X := by
  change (MvPolynomial.uniqueAlgEquiv K Unit)
    ((SymmetricAlgebra.equivMvPolynomial (Module.Basis.singleton Unit K))
      (SymmetricAlgebra.ι K K 1)) = Polynomial.X
  have h := SymmetricAlgebra.equivMvPolynomial_ι_apply
    (Module.Basis.singleton Unit K) default
  simp only [Module.Basis.singleton_apply] at h
  rw [h]
  simp

instance additiveGroupCoordinateRing_finiteType
    (K : Type u) [CommRing K] :
    Algebra.FiniteType K (additiveGroupCoordinateRing K) :=
  Algebra.FiniteType.equiv
    (inferInstance : Algebra.FiniteType K (Polynomial K))
    (additiveGroupCoordinateAlgEquiv K).symm

/-- The underlying affine scheme over `K` represented by the rank-one symmetric
algebra. -/
abbrev additiveGroupUnderlyingScheme
    (K : Type u) [CommRing K] : Over (Spec (.of K)) :=
  (Spec (.of (additiveGroupCoordinateRing K))).asOver (Spec (.of K))

instance additiveGroupUnderlyingScheme_locallyOfFiniteType
    (K : Type u) [CommRing K] :
    LocallyOfFiniteType (additiveGroupUnderlyingScheme K).hom := by
  let _ : Algebra.FiniteType K (additiveGroupCoordinateRing K) :=
    additiveGroupCoordinateRing_finiteType K
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
    (algebraMap K (additiveGroupCoordinateRing K))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  simpa [RingHom.finiteType_algebraMap]

instance additiveGroupUnderlyingScheme_quasiCompact
    (K : Type u) [CommRing K] :
    QuasiCompact (additiveGroupUnderlyingScheme K).hom := by
  change QuasiCompact (Spec.map (CommRingCat.ofHom
    (algebraMap K (additiveGroupCoordinateRing K))))
  infer_instance

/-- The additive group scheme over `K`. -/
abbrev additiveGroupScheme
    (K : Type u) [CommRing K] : Grp (Over (Spec (.of K))) :=
  ⟨additiveGroupUnderlyingScheme K⟩

/-- The group-valued functor sending a `K`-algebra to its additive group.
`Multiplicative` changes only the operation tag required by `GrpCat`. -/
@[expose] def additiveGroupFunctor
    (K : Type u) [CommRing K] : CommAlgCat K ⥤ GrpCat where
  obj R := GrpCat.of (Multiplicative R)
  map f := GrpCat.ofHom (AddMonoidHom.toMultiplicative f.hom.toAddMonoidHom)
  map_id _ := by
    apply GrpCat.hom_ext
    rfl
  map_comp _ _ := by
    apply GrpCat.hom_ext
    rfl

/-- The group-valued functor of points of the additive group scheme, restricted
to affine test schemes. -/
abbrev additiveGroupPointsFunctor
    (K : Type u) [CommRing K] : CommAlgCat K ⥤ GrpCat :=
  (algSpec (.of K)).rightOp ⋙ yonedaGrp.obj (additiveGroupScheme K)

variable (K R : Type u) [CommRing K] [CommRing R] [Algebra K R]

private def additiveGroupEquivAlgHom :
    Multiplicative R ≃
      WithConv (additiveGroupCoordinateRing K →ₐ[K] R) :=
  (LinearMap.ringLmapEquivSelf K K R).symm.toEquiv.trans <|
    (SymmetricAlgebra.lift.trans (WithConv.equiv _).symm)

private lemma additiveGroupEquivAlgHom_apply (r : Multiplicative R) :
    (additiveGroupEquivAlgHom K R r).ofConv =
      SymmetricAlgebra.lift
        ((LinearMap.ringLmapEquivSelf K K R).symm r.toAdd) :=
  rfl

/-- Additive elements are multiplicatively equivalent to algebra maps out of the
additive-group coordinate ring, equipped with convolution. -/
@[expose] def additiveGroupMulEquivAlgHom :
    Multiplicative R ≃*
      WithConv (additiveGroupCoordinateRing K →ₐ[K] R) where
  toEquiv :=
    (LinearMap.ringLmapEquivSelf K K R).symm.toEquiv.trans <|
      (SymmetricAlgebra.lift.trans (WithConv.equiv _).symm)
  map_mul' r s := by
    apply WithConv.ofConv_injective
    apply SymmetricAlgebra.algHom_ext
    ext
    change (additiveGroupEquivAlgHom K R (r * s)).ofConv
        (SymmetricAlgebra.ι K K 1) =
      ((additiveGroupEquivAlgHom K R r) *
        (additiveGroupEquivAlgHom K R s)).ofConv
          (SymmetricAlgebra.ι K K 1)
    rw [show (additiveGroupEquivAlgHom K R (r * s)).ofConv =
        SymmetricAlgebra.lift
          ((LinearMap.ringLmapEquivSelf K K R).symm (r * s).toAdd) by rfl,
      AlgHom.convMul_apply, SymmetricAlgebra.comul_ι]
    simp [additiveGroupEquivAlgHom_apply]

/-- Under the additive-element/algebra-map equivalence, evaluation at the
distinguished coordinate recovers the original element. -/
@[simp]
theorem additiveGroupMulEquivAlgHom_coordinate (r : R) :
    (additiveGroupMulEquivAlgHom K R (.ofAdd r)).ofConv
        (additiveGroupCoordinate K) = r := by
  rw [show (additiveGroupMulEquivAlgHom K R (.ofAdd r)).ofConv =
      SymmetricAlgebra.lift ((LinearMap.ringLmapEquivSelf K K R).symm r) by rfl]
  simp [additiveGroupCoordinate]

/-- Naturality of the additive-element/algebra-map equivalence under a map of
base algebras. -/
theorem additiveGroupMulEquivAlgHom_naturality
    {S : Type u} [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) (r : R) :
    (additiveGroupMulEquivAlgHom K S (.ofAdd (f r))).ofConv =
      f.comp (additiveGroupMulEquivAlgHom K R (.ofAdd r)).ofConv := by
  apply SymmetricAlgebra.algHom_ext
  ext
  rw [show (additiveGroupMulEquivAlgHom K S (.ofAdd (f r))).ofConv =
      SymmetricAlgebra.lift ((LinearMap.ringLmapEquivSelf K K S).symm (f r)) by rfl,
    show (additiveGroupMulEquivAlgHom K R (.ofAdd r)).ofConv =
      SymmetricAlgebra.lift ((LinearMap.ringLmapEquivSelf K K R).symm r) by rfl]
  simp

/-- The functor-of-points equivalence at a `K`-algebra `R`. -/
@[expose] def additiveGroupMulEquivPoints :
    Multiplicative R ≃*
      ((Spec (.of R)).asOver (Spec (.of K)) ⟶ (additiveGroupScheme K).X) :=
  (additiveGroupMulEquivAlgHom K R).trans
    (Spec.mapMulEquiv
      (R := K) (S := additiveGroupCoordinateRing K) (T := R))

/-- The underlying scheme map of an additive-group point is induced by its
corresponding coordinate-algebra homomorphism. -/
@[simp]
theorem additiveGroupMulEquivPoints_apply_left (r : R) :
    (additiveGroupMulEquivPoints K R (.ofAdd r)).left =
      Spec.map (CommRingCat.ofHom
        (additiveGroupMulEquivAlgHom K R (.ofAdd r)).ofConv.toRingHom) :=
  rfl

/-- The affine additive group scheme represents the additive-group functor.
This extends the field-base additive group of Milne, *Algebraic Groups*
(2017), item 2.1, to an arbitrary commutative base ring. -/
@[expose] def additiveGroupPointsIso
    (K : Type u) [CommRing K] :
    additiveGroupFunctor K ≅ additiveGroupPointsFunctor K :=
  NatIso.ofComponents
    (fun R ↦ (additiveGroupMulEquivPoints K R).toGrpIso)
    (fun {R S} f ↦ by
      ext r
      apply Over.OverMorphism.ext
      change
        (additiveGroupMulEquivPoints K S (.ofAdd (f.hom r))).left =
          ((algSpec (.of K)).map f.op).left ≫
            (additiveGroupMulEquivPoints K R (.ofAdd r)).left
      rw [additiveGroupMulEquivPoints_apply_left]
      change
        Spec.map (CommRingCat.ofHom
          (additiveGroupMulEquivAlgHom K S
            (.ofAdd (f.hom r))).ofConv.toRingHom) =
          Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
            Spec.map (CommRingCat.ofHom
              (additiveGroupMulEquivAlgHom K R (.ofAdd r)).ofConv.toRingHom)
      rw [← Spec.map_comp]
      congr 1
      exact congrArg (fun h : additiveGroupCoordinateRing K →ₐ[K] S ↦
          CommRingCat.ofHom h.toRingHom)
        (additiveGroupMulEquivAlgHom_naturality K R f.hom r))

/-- Comultiplication makes the distinguished coordinate primitive, as for
Milne's `T` in *Algebraic Groups* (2017), item 2.1. -/
@[simp]
theorem additiveGroupCoordinate_comul
    (K : Type u) [CommRing K] :
    CoalgebraStruct.comul (additiveGroupCoordinate K) =
      additiveGroupCoordinate K ⊗ₜ[K] 1 +
        1 ⊗ₜ[K] additiveGroupCoordinate K := by
  exact SymmetricAlgebra.comul_ι K K 1

/-- The counit sends the distinguished coordinate to zero. -/
@[simp]
theorem additiveGroupCoordinate_counit
    (K : Type u) [CommRing K] :
    CoalgebraStruct.counit (R := K) (additiveGroupCoordinate K) = (0 : K) := by
  exact SymmetricAlgebra.counit_ι K K 1

/-- The antipode negates the distinguished coordinate. -/
@[simp]
theorem additiveGroupCoordinate_antipode
    (K : Type u) [CommRing K] :
    (HopfAlgebraStruct.antipode K) (additiveGroupCoordinate K) =
      -additiveGroupCoordinate K := by
  exact SymmetricAlgebra.antipode_ι K K 1

end AlgebraicGeometry
