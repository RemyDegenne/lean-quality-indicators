public section

noncomputable section

open CategoryTheory

open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

variable (K R : Type u) [CommRing K] [CommRing R] [Algebra K R]

@[simp]
theorem additiveGroupMulEquivAlgHom_coordinate (r : R) :
    (additiveGroupMulEquivAlgHom K R (.ofAdd r)).ofConv
        (additiveGroupCoordinate K) = r := by
  rw [show (additiveGroupMulEquivAlgHom K R (.ofAdd r)).ofConv =
      SymmetricAlgebra.lift ((LinearMap.ringLmapEquivSelf K K R).symm r) by rfl]
  simp [additiveGroupCoordinate]

end AlgebraicGeometry
end
end
