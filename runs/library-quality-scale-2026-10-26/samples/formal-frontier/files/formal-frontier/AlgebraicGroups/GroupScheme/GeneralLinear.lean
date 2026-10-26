/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.GeneralLinearCoordinateRing
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# The finite general linear group scheme

The determinant localization represents invertible square matrices over every
commutative algebra. Its Hopf structure induces a finite-type group scheme whose
affine points agree naturally, as groups, with invertible matrices. The group
law is matrix multiplication, realized by convolution on coordinate evaluations;
the represented points are morphisms from `Spec R`, not functions on field-valued
points.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2, item 2.8, p. 41: the finite
  general linear group represented by determinant localization over a field.
* Mathlib, `AlgebraicGeometry/Group/Affine`: Hopf-algebra `Spec`, the algebraic
  group of affine points, and `Spec.mapMulEquiv`.
* Mathlib, `RingTheory/Bialgebra/Convolution` and
  `CategoryTheory/Monoidal/Cartesian/Grp`: convolution multiplication of
  algebra maps and the group-valued Yoneda functor.
* Mathlib, `LinearAlgebra/Matrix/GeneralLinearGroup/Defs`,
  `AlgebraicGeometry/Morphisms/FiniteType`, and
  `AlgebraicGeometry/Morphisms/Affine`: coefficient change for invertible
  matrices, finite-type `Spec` morphisms, and quasi-compact affine morphisms.
-/

@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- The underlying affine scheme over `Spec K`. -/
abbrev generalLinearGroupUnderlyingScheme : Over (Spec (.of K)) :=
  (Spec (.of (CoordinateRing K n))).asOver (Spec (.of K))

instance generalLinearGroupUnderlyingScheme_locallyOfFiniteType :
    LocallyOfFiniteType (generalLinearGroupUnderlyingScheme K n).hom := by
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
    (algebraMap K (CoordinateRing K n))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  change (algebraMap K (CoordinateRing K n)).FiniteType
  exact RingHom.finiteType_algebraMap.mpr (GeneralLinearCoordinateRing.finiteType K n)

instance generalLinearGroupUnderlyingScheme_quasiCompact :
    QuasiCompact (generalLinearGroupUnderlyingScheme K n).hom := by
  change QuasiCompact (Spec.map (CommRingCat.ofHom
    (algebraMap K (CoordinateRing K n))))
  infer_instance

/-- The group object represented by the determinant-localized Hopf algebra. -/
abbrev generalLinearGroupScheme : Grp (Over (Spec (.of K))) :=
  ⟨generalLinearGroupUnderlyingScheme K n⟩

/-- Invertible matrices, functorial in every `K`-algebra. -/
def generalLinearGroupFunctor : CommAlgCat K ⥤ GrpCat where
  obj R := GrpCat.of (Matrix.GeneralLinearGroup n R)
  map f := GrpCat.ofHom (Matrix.GeneralLinearGroup.map f.hom.toRingHom)
  map_id R := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl
  map_comp f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro matrix
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl

/-- Group-valued affine points of the GL group scheme. -/
abbrev generalLinearGroupPointsFunctor : CommAlgCat K ⥤ GrpCat :=
  (algSpec (.of K)).rightOp ⋙ yonedaGrp.obj (generalLinearGroupScheme K n)

variable (R : Type u) [CommRing R] [Algebra K R]

theorem generalLinearConvMul_matrix
    (f g : CoordinateRing K n →ₐ[K] R) (i j : n) :
    ((WithConv.toConv f * WithConv.toConv g).ofConv) (matrix K n i j) =
      ∑ index : n, f (matrix K n i index) * g (matrix K n index j) := by
  change (WithConv.toConv f * WithConv.toConv g) (matrix K n i j) = _
  rw [AlgHom.convMul_apply, native_comul_matrix]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro index _
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

/-- Multiplication of the matrices represented by Milne's determinant
localization (item 2.8) agrees with convolution through its ordered coproduct. -/
def generalLinearGroupMulEquivAlgHom :
    Matrix.GeneralLinearGroup n R ≃* WithConv (CoordinateRing K n →ₐ[K] R) where
  toFun g := WithConv.toConv (evaluate (K := K) g)
  invFun φ := toGL φ.ofConv
  left_inv g := toGL_evaluate g
  right_inv φ := by
    apply WithConv.ofConv_injective
    exact evaluate_toGL φ.ofConv
  map_mul' g h := by
    apply WithConv.ofConv_injective
    apply hom_ext (K := K) (n := n)
    intro i j
    rw [generalLinearConvMul_matrix]
    rw [evaluate_matrix]
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, evaluate_matrix]

theorem generalLinearGroupMulEquivAlgHom_apply_matrix
    (g : Matrix.GeneralLinearGroup n R) (i j : n) :
    (generalLinearGroupMulEquivAlgHom K n R g).ofConv (matrix K n i j) = g i j :=
  evaluate_matrix g i j

@[simp] theorem generalLinearGroupMulEquivAlgHom_apply_detInverse
    (g : Matrix.GeneralLinearGroup n R) :
    (generalLinearGroupMulEquivAlgHom K n R g).ofConv (detInverse K n) =
      ↑(Matrix.GeneralLinearGroup.det g)⁻¹ := evaluate_detInverse g

/-- The multiplication-preserving comparison with affine `Spec` points. -/
def generalLinearGroupMulEquivPoints :
    Matrix.GeneralLinearGroup n R ≃*
      ((Spec (.of R)).asOver (Spec (.of K)) ⟶ generalLinearGroupUnderlyingScheme K n) :=
  (generalLinearGroupMulEquivAlgHom K n R).trans
    (Spec.mapMulEquiv (R := K) (S := CoordinateRing K n) (T := R))

/-- Read back the underlying `Spec.map` of a matrix point. -/
@[simp] theorem generalLinearGroupMulEquivPoints_apply_left
    (g : Matrix.GeneralLinearGroup n R) :
    (generalLinearGroupMulEquivPoints K n R g).left =
      Spec.map (CommRingCat.ofHom
        (generalLinearGroupMulEquivAlgHom K n R g).ofConv.toRingHom) := rfl

/-- Pulling back an entry coordinate along the corresponding affine point
returns that matrix entry. -/
theorem generalLinearGroupPoint_preimage_entry
    (g : Matrix.GeneralLinearGroup n R) (i j : n) :
    (Spec.preimage (generalLinearGroupMulEquivPoints K n R g).left).hom
      (matrix K n i j) = g i j := by
  rw [generalLinearGroupMulEquivPoints_apply_left, Spec.preimage_map]
  exact generalLinearGroupMulEquivAlgHom_apply_matrix K n R g i j

/-- The same point evaluates the inverse determinant coordinate. -/
theorem generalLinearGroupPoint_preimage_detInverse
    (g : Matrix.GeneralLinearGroup n R) :
    (Spec.preimage (generalLinearGroupMulEquivPoints K n R g).left).hom
      (detInverse K n) = ↑(Matrix.GeneralLinearGroup.det g)⁻¹ := by
  rw [generalLinearGroupMulEquivPoints_apply_left, Spec.preimage_map]
  exact generalLinearGroupMulEquivAlgHom_apply_detInverse K n R g

/-- Over every commutative base and test algebra, the finite matrix general
linear group is naturally the group of affine points of its representing scheme;
compare Milne, *Algebraic Groups*, item 2.8, over a field. -/
def generalLinearGroupPointsIso :
    generalLinearGroupFunctor K n ≅ generalLinearGroupPointsFunctor K n :=
  NatIso.ofComponents
    (fun R ↦ (generalLinearGroupMulEquivPoints K n R).toGrpIso)
    (fun {R S} f ↦ by
      ext g
      apply Over.OverMorphism.ext
      change
        (generalLinearGroupMulEquivPoints K n S
          (Matrix.GeneralLinearGroup.map f.hom.toRingHom g)).left =
          ((algSpec (.of K)).map f.op).left ≫
            (generalLinearGroupMulEquivPoints K n R g).left
      rw [generalLinearGroupMulEquivPoints_apply_left]
      change
        Spec.map (CommRingCat.ofHom
          (evaluate (K := K)
            (Matrix.GeneralLinearGroup.map f.hom.toRingHom g)).toRingHom) =
          Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
            Spec.map (CommRingCat.ofHom (evaluate (K := K) g).toRingHom)
      rw [← Spec.map_comp]
      congr 1
      exact congrArg (fun h : CoordinateRing K n →ₐ[K] S ↦ CommRingCat.ofHom h.toRingHom)
        (evaluate_natural f.hom g))

end AlgebraicGeometry

#lint
