/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# The multiplicative group scheme

This file packages the affine group scheme over an arbitrary commutative base
represented by the Laurent polynomial Hopf algebra. Its affine points are
naturally the groups of units, and its distinguished coordinate is invertible
and group-like.

Milne's *Algebraic Groups*, item 2.2, gives the units functor over a field,
represented by `k[T,T⁻¹]` with `Δ(T) = T ⊗ T`. Here the construction and
representability extend to any commutative base ring, including the zero ring.

## Main definitions

- `AlgebraicGeometry.multiplicativeGroupScheme`
- `AlgebraicGeometry.multiplicativeGroupMulEquivAlgHom`
- `AlgebraicGeometry.multiplicativeGroupMulEquivPoints`
- `AlgebraicGeometry.multiplicativeGroupPointsIso`

## References

- James S. Milne, *Algebraic Groups* (2017), item 2.2, p. 40 (the units
  functor, Laurent coordinate ring, and comultiplication on its coordinate).
- Mathlib, `Mathlib.Algebra.Polynomial.Laurent`,
  `Mathlib.Algebra.MonoidAlgebra.Basic`,
  `Mathlib.RingTheory.Bialgebra.MonoidAlgebra`, and
  `Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra` (Laurent coordinates, lifted
  algebra maps, convolution, and the Hopf-algebra structure).
- Mathlib, `Mathlib.AlgebraicGeometry.Group.Affine` (the affine Hopf-algebra
  construction and the affine `Spec` points/convolution equivalence used here).
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

universe u v w

namespace AlgebraicGeometry

/-- The Laurent-polynomial coordinate ring of the multiplicative group,
extending the field-base presentation in Milne's *Algebraic Groups*, item 2.2. -/
abbrev multiplicativeGroupCoordinateRing
    (K : Type u) [CommRing K] := LaurentPolynomial K

/-- The distinguished invertible coordinate of the multiplicative group. -/
def multiplicativeGroupCoordinate
    (K : Type u) [CommRing K] : multiplicativeGroupCoordinateRing K :=
  LaurentPolynomial.T 1

instance multiplicativeGroupCoordinateRing_finiteType
    (K : Type u) [CommRing K] :
    Algebra.FiniteType K (multiplicativeGroupCoordinateRing K) := by
  let _ : AddMonoid.FG ℤ := AddGroup.fg_iff_addMonoid_fg.mp inferInstance
  exact AddMonoidAlgebra.finiteType_of_fg K ℤ

/-- The underlying affine scheme over `K` represented by its Laurent-polynomial
coordinate ring. -/
abbrev multiplicativeGroupUnderlyingScheme
    (K : Type u) [CommRing K] : Over (Spec (.of K)) :=
  (Spec (.of (multiplicativeGroupCoordinateRing K))).asOver (Spec (.of K))

instance multiplicativeGroupUnderlyingScheme_locallyOfFiniteType
    (K : Type u) [CommRing K] :
    LocallyOfFiniteType (multiplicativeGroupUnderlyingScheme K).hom := by
  let _ : Algebra.FiniteType K (multiplicativeGroupCoordinateRing K) :=
    multiplicativeGroupCoordinateRing_finiteType K
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
    (algebraMap K (multiplicativeGroupCoordinateRing K))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  simpa [RingHom.finiteType_algebraMap]

instance multiplicativeGroupUnderlyingScheme_quasiCompact
    (K : Type u) [CommRing K] :
    QuasiCompact (multiplicativeGroupUnderlyingScheme K).hom := by
  change QuasiCompact (Spec.map (CommRingCat.ofHom
    (algebraMap K (multiplicativeGroupCoordinateRing K))))
  infer_instance

/-- The multiplicative group scheme over `K`, extending Milne's *Algebraic
Groups*, item 2.2, from fields to commutative rings. -/
abbrev multiplicativeGroupScheme
    (K : Type u) [CommRing K] : Grp (Over (Spec (.of K))) :=
  ⟨multiplicativeGroupUnderlyingScheme K⟩

/-- The group-valued functor sending a `K`-algebra to its group of units. -/
def multiplicativeGroupFunctor
    (K : Type u) [CommRing K] : CommAlgCat K ⥤ GrpCat where
  obj R := GrpCat.of ((R : Type u)ˣ)
  map f := GrpCat.ofHom (Units.map f.hom)
  map_id R := by
    ext u
    rfl
  map_comp f g := by
    ext u
    rfl

/-- The group-valued functor of points of the multiplicative group scheme,
restricted to affine test schemes. -/
abbrev multiplicativeGroupPointsFunctor
    (K : Type u) [CommRing K] : CommAlgCat K ⥤ GrpCat :=
  (algSpec (.of K)).rightOp ⋙ yonedaGrp.obj (multiplicativeGroupScheme K)

variable (K : Type u) [CommRing K]

section AlgebraMaps

variable (R : Type v) [CommSemiring R] [Algebra K R]

/-- Units are multiplicatively equivalent to algebra maps out of the
Laurent-polynomial coordinate ring, equipped with convolution. This realizes
the representing algebra of Milne's *Algebraic Groups*, item 2.2, over
arbitrary commutative base rings. -/
def multiplicativeGroupMulEquivAlgHom :
    Rˣ ≃* WithConv (multiplicativeGroupCoordinateRing K →ₐ[K] R) where
  toFun u := WithConv.toConv
    (AddMonoidAlgebra.lift K R ℤ
      ((zpowersMulHom Rˣ).trans
        (@MonoidHom.toHomUnitsMulEquiv (Multiplicative ℤ) R _ _).symm u))
  invFun φ := ((zpowersMulHom Rˣ).trans
      (@MonoidHom.toHomUnitsMulEquiv (Multiplicative ℤ) R _ _).symm).symm
    ((AddMonoidAlgebra.lift K R ℤ).symm φ.ofConv)
  left_inv u := by
    change ((zpowersMulHom Rˣ).trans
        (@MonoidHom.toHomUnitsMulEquiv (Multiplicative ℤ) R _ _).symm).symm
      ((AddMonoidAlgebra.lift K R ℤ).symm
        (AddMonoidAlgebra.lift K R ℤ
          ((zpowersMulHom Rˣ).trans
            (@MonoidHom.toHomUnitsMulEquiv (Multiplicative ℤ) R _ _).symm u))) = u
    rw [Equiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  right_inv φ := by
    apply WithConv.ofConv_injective
    change AddMonoidAlgebra.lift K R ℤ
        (((zpowersMulHom Rˣ).trans
          (@MonoidHom.toHomUnitsMulEquiv (Multiplicative ℤ) R _ _).symm)
          (((zpowersMulHom Rˣ).trans
            (@MonoidHom.toHomUnitsMulEquiv (Multiplicative ℤ) R _ _).symm).symm
            ((AddMonoidAlgebra.lift K R ℤ).symm φ.ofConv))) = φ.ofConv
    rw [MulEquiv.apply_symm_apply, Equiv.apply_symm_apply]
  map_mul' u v := by
    apply WithConv.ofConv_injective
    ext n
    rw [AddMonoidAlgebra.convMul_algHom_single_one]
    change
      (AddMonoidAlgebra.lift K R ℤ
        ((zpowersMulHom Rˣ).trans
          (@MonoidHom.toHomUnitsMulEquiv (Multiplicative ℤ) R _ _).symm (u * v)))
          (AddMonoidAlgebra.single n 1) =
        (AddMonoidAlgebra.lift K R ℤ
          ((zpowersMulHom Rˣ).trans
            (@MonoidHom.toHomUnitsMulEquiv (Multiplicative ℤ) R _ _).symm u))
            (AddMonoidAlgebra.single n 1) *
          (AddMonoidAlgebra.lift K R ℤ
            ((zpowersMulHom Rˣ).trans
              (@MonoidHom.toHomUnitsMulEquiv (Multiplicative ℤ) R _ _).symm v))
              (AddMonoidAlgebra.single n 1)
    rw [AddMonoidAlgebra.lift_single, AddMonoidAlgebra.lift_single,
      AddMonoidAlgebra.lift_single]
    simp

/-- Under the units/algebra-map equivalence, evaluation at the distinguished
coordinate recovers the original unit. -/
@[simp]
theorem multiplicativeGroupMulEquivAlgHom_coordinate (u : Rˣ) :
    (multiplicativeGroupMulEquivAlgHom K R u).ofConv
        (multiplicativeGroupCoordinate K) = u := by
  change AddMonoidAlgebra.lift K R ℤ
      ((zpowersMulHom Rˣ).trans
        (@MonoidHom.toHomUnitsMulEquiv (Multiplicative ℤ) R _ _).symm u)
        (AddMonoidAlgebra.single 1 1) = ↑u
  rw [AddMonoidAlgebra.lift_single]
  simp

/-- Naturality of the units/algebra-map equivalence under a map of base
algebras. -/
theorem multiplicativeGroupMulEquivAlgHom_naturality
    {S : Type w} [CommSemiring S] [Algebra K S]
    (f : R →ₐ[K] S) (u : Rˣ) :
    (multiplicativeGroupMulEquivAlgHom K S (Units.map f u)).ofConv =
      f.comp (multiplicativeGroupMulEquivAlgHom K R u).ofConv := by
  apply AddMonoidAlgebra.algHom_ext
  · intro n
    change
      (AddMonoidAlgebra.lift K S ℤ
        ((Units.coeHom S).comp (zpowersMulHom Sˣ (Units.map f u))))
          (AddMonoidAlgebra.single n 1) =
        f ((AddMonoidAlgebra.lift K R ℤ
          ((Units.coeHom R).comp (zpowersMulHom Rˣ u)))
            (AddMonoidAlgebra.single n 1))
    rw [AddMonoidAlgebra.lift_single, AddMonoidAlgebra.lift_single]
    simp only [one_smul, MonoidHom.coe_comp, Function.comp_apply,
      zpowersMulHom_apply, toAdd_ofAdd]
    rw [Units.coeHom_apply, Units.coeHom_apply]
    calc
      ↑((Units.map (f : R →* S)) u ^ n) =
          ↑(Units.map (f : R →* S) (u ^ n)) :=
        congrArg Units.val (map_zpow (Units.map (f : R →* S)) u n).symm
      _ = f ↑(u ^ n) := Units.coe_map (f : R →* S) (u ^ n)
  · ext

end AlgebraMaps

section AffinePoints

variable (R : Type u) [CommRing R] [Algebra K R]

/-- The functor-of-points equivalence at a `K`-algebra `R`, extending the
units-valued points of Milne's *Algebraic Groups*, item 2.2. -/
def multiplicativeGroupMulEquivPoints :
    Rˣ ≃* ((Spec (.of R)).asOver (Spec (.of K)) ⟶
      multiplicativeGroupUnderlyingScheme K) :=
  (multiplicativeGroupMulEquivAlgHom K R).trans
    (Spec.mapMulEquiv
      (R := K) (S := multiplicativeGroupCoordinateRing K) (T := R))

/-- The underlying scheme map of a multiplicative-group point is induced by
its corresponding coordinate-algebra homomorphism. -/
@[simp]
theorem multiplicativeGroupMulEquivPoints_apply_left (u : Rˣ) :
    (multiplicativeGroupMulEquivPoints K R u).left =
      Spec.map (CommRingCat.ofHom
        (multiplicativeGroupMulEquivAlgHom K R u).ofConv.toRingHom) :=
  rfl

end AffinePoints

/-- The affine multiplicative group scheme represents the units functor.
This extends Milne's *Algebraic Groups*, item 2.2, to arbitrary commutative
base rings and makes the point equivalences natural in the test algebra. -/
def multiplicativeGroupPointsIso
    (K : Type u) [CommRing K] :
    multiplicativeGroupFunctor K ≅ multiplicativeGroupPointsFunctor K :=
  NatIso.ofComponents
    (fun R ↦ (multiplicativeGroupMulEquivPoints K R).toGrpIso)
    (fun {R S} f ↦ by
      ext u
      apply Over.OverMorphism.ext
      change
        (multiplicativeGroupMulEquivPoints K S (Units.map f.hom u)).left =
          ((algSpec (.of K)).map f.op).left ≫
            (multiplicativeGroupMulEquivPoints K R u).left
      rw [multiplicativeGroupMulEquivPoints_apply_left]
      change
        Spec.map (CommRingCat.ofHom
          (multiplicativeGroupMulEquivAlgHom K S
            (Units.map f.hom u)).ofConv.toRingHom) =
          Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
            Spec.map (CommRingCat.ofHom
              (multiplicativeGroupMulEquivAlgHom K R u).ofConv.toRingHom)
      rw [← Spec.map_comp]
      congr 1
      exact congrArg (fun h : multiplicativeGroupCoordinateRing K →ₐ[K] S ↦
          CommRingCat.ofHom h.toRingHom)
        (multiplicativeGroupMulEquivAlgHom_naturality K R f.hom u))

/-- The distinguished coordinate is a unit. -/
@[simp]
theorem multiplicativeGroupCoordinate_isUnit
    (K : Type u) [CommRing K] :
    IsUnit (multiplicativeGroupCoordinate K) := by
  exact LaurentPolynomial.isUnit_T 1

/-- Comultiplication sends the distinguished coordinate to its tensor square,
as in Milne's *Algebraic Groups*, item 2.2. This uses Mathlib's
`LaurentPolynomial.comul_T`. -/
@[simp]
theorem multiplicativeGroupCoordinate_comul
    (K : Type u) [CommRing K] :
    CoalgebraStruct.comul (multiplicativeGroupCoordinate K) =
      multiplicativeGroupCoordinate K ⊗ₜ[K] multiplicativeGroupCoordinate K := by
  exact LaurentPolynomial.comul_T 1

/-- The counit sends the distinguished coordinate to one. -/
@[simp]
theorem multiplicativeGroupCoordinate_counit
    (K : Type u) [CommRing K] :
    CoalgebraStruct.counit (R := K) (multiplicativeGroupCoordinate K) = (1 : K) := by
  exact LaurentPolynomial.counit_T 1

/-- The antipode sends the distinguished coordinate to its inverse. -/
@[simp]
theorem multiplicativeGroupCoordinate_antipode
    (K : Type u) [CommRing K] :
    (HopfAlgebraStruct.antipode K) (multiplicativeGroupCoordinate K) =
      LaurentPolynomial.T (-1) := by
  exact LaurentPolynomial.antipode_T 1

end AlgebraicGeometry
