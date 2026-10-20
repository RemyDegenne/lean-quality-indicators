@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing SpecialLinearCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

variable (R : Type u) [CommRing R] [Algebra K R]

theorem specialLinearInclusion_point (s : Matrix.SpecialLinearGroup n R) :
    specialLinearGroupMulEquivPoints K n R s ≫ (specialLinearInclusion K n).hom.hom =
      generalLinearGroupMulEquivPoints K n R (Matrix.SpecialLinearGroup.toGL s) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, specialLinearGroupMulEquivPoints_apply_left,
    specialLinearInclusion_left, generalLinearGroupMulEquivPoints_apply_left]
  change Spec.map (CommRingCat.ofHom (specialLinearFromSL K n R s).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (quotient K n).toRingHom) =
    Spec.map (CommRingCat.ofHom
      (evaluate (K := K) (Matrix.SpecialLinearGroup.toGL s)).toRingHom)
  rw [← Spec.map_comp]
  exact congrArg (fun hom : GeneralLinearCoordinateRing.CoordinateRing K n →ₐ[K] R ↦
    Spec.map (CommRingCat.ofHom hom.toRingHom))
      (specialLinearFromSL_comp_quotient K n R s)

end AlgebraicGeometry
end
end
