@[expose] public section

noncomputable section

namespace ProjectiveSpace

universe u v

variable {k : Type u} [Field k] {ι : Type v}

attribute [local instance] MvPolynomial.gradedAlgebra

@[simp]
theorem projectivizationToProj_mk (a : ι → k) (ha : a ≠ 0) :
    projectivizationToProj (Projectivization.mk k a ha) =
      homogeneousCoordinatePoint a ha :=
  rfl

end ProjectiveSpace
end
end
