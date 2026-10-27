@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing SpecialLinearCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

variable (R : Type u) [CommRing R] [Algebra K R]

/-- The native finite special linear group is its represented functor of points;
the field-base determinant-one coordinate description occurs in Milne,
*Basic Theory of Affine Group Schemes*, VII §4, Example 4.3. The natural
all-algebra group equivalence uses Mathlib's Hopf-Spec and native matrix SL. -/
def specialLinearGroupPointsIso :
    specialLinearGroupFunctor K n ≅ specialLinearGroupPointsFunctor K n :=
  NatIso.ofComponents
    (fun R ↦ (specialLinearGroupMulEquivPoints K n R).toGrpIso)
    (fun {R S} f ↦ by
      ext s
      apply Over.OverMorphism.ext
      change
        (specialLinearGroupMulEquivPoints K n S
          (Matrix.SpecialLinearGroup.map f.hom.toRingHom s)).left =
            ((algSpec (.of K)).map f.op).left ≫
              (specialLinearGroupMulEquivPoints K n R s).left
      rw [specialLinearGroupMulEquivPoints_apply_left]
      change Spec.map (CommRingCat.ofHom
        (specialLinearFromSL K n S
          (Matrix.SpecialLinearGroup.map f.hom.toRingHom s)).toRingHom) =
          Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
            Spec.map (CommRingCat.ofHom (specialLinearFromSL K n R s).toRingHom)
      rw [← Spec.map_comp]
      exact congrArg (fun h : SpecialLinearCoordinateRing.CoordinateRing K n →ₐ[K] S ↦
        Spec.map (CommRingCat.ofHom h.toRingHom))
          (specialLinearFromSL_natural K n R f.hom s))

end AlgebraicGeometry
end
end
