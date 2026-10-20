public section

noncomputable section

open AlgebraicGeometry CategoryTheory

open scoped ProjectiveSpace

namespace ProjectiveSpace

universe u v

variable {k : Type u} [Field k] {ι : Type v}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The affine coordinates obtained by normalizing the `i`th homogeneous
coordinate to one. -/
@[expose] def normalizedCoordinates (a : ι → k) (i : ι) : {j : ι // j ≠ i} → k :=
  fun j ↦ a j.1 / a i

end ProjectiveSpace
end
end
