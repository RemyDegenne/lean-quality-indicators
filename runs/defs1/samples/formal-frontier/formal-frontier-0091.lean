set_option warningAsError true

public section

open AlgebraicGeometry

namespace ProjectiveSpace

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

universe u v w

variable {R : Type u} {M : Type v}

variable [CommRing R] [AddCommGroup M] [Module R M]

variable {I : Type w}

/-- A basis identifies the closed points of polynomial projective space with
those of the `Proj` of the symmetric algebra, with no common-universe
requirement on the basis index and module. -/
@[expose] noncomputable def mvPolynomialProjClosedPointsEquivSymmetricAlgebra
    (b : Module.Basis I R M) :
    closedPoints (Proj (MvPolynomial.homogeneousSubmodule I R)) ≃
      closedPoints
        (Proj (SymmetricAlgebra.homogeneousSubmodule (R := R) (M := M))) :=
  projClosedPointsEquivOfInverseGradedRingHom
    (𝒜 := SymmetricAlgebra.homogeneousSubmodule (R := R) (M := M))
    (ℬ := MvPolynomial.homogeneousSubmodule I R)
    (SymmetricAlgebra.equivMvPolynomialGradedHom b).toGradedRingHom
    (SymmetricAlgebra.equivMvPolynomialSymmGradedHom b).toGradedRingHom
    (symmetricAlgebraGradedHom_comp_mvPolynomialGradedHom b)
    (mvPolynomialGradedHom_comp_symmetricAlgebraGradedHom b)

end
end ProjectiveSpace
end
