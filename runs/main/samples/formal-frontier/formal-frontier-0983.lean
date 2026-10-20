@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

variable (R : Type u) [CommRing R] [Algebra K R]

@[simp] theorem generalLinearGroupMulEquivPoints_apply_left
    (g : Matrix.GeneralLinearGroup n R) :
    (generalLinearGroupMulEquivPoints K n R g).left =
      Spec.map (CommRingCat.ofHom
        (generalLinearGroupMulEquivAlgHom K n R g).ofConv.toRingHom) := rfl

end AlgebraicGeometry
end
end
