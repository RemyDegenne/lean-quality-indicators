@[expose] public section

noncomputable section

namespace ProjectiveSpace

universe u v

variable {k : Type u} [Field k] {ι : Type v}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The homogeneous-coordinate ideal represented by `a`. It is the kernel of
the cone-line evaluation map `X i ↦ a i * t`. -/
noncomputable def homogeneousCoordinateIdeal (a : ι → k) :
    Ideal (MvPolynomial ι k) :=
  RingHom.ker (homogeneousCoordinateMap a).toRingHom

end ProjectiveSpace
end
end
