set_option warningAsError true

public section

open AlgebraicGeometry

namespace ProjectiveSpace

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

universe u v w

variable {R : Type u} {M : Type v}

variable [CommRing R] [AddCommGroup M] [Module R M]

section LinearEquivScheme

variable {N : Type v} [AddCommGroup N] [Module R N]

/-- A linear equivalence between modules in a common universe induces the
contravariant scheme isomorphism of `Proj` of their symmetric algebras. The
common module universe is exactly the current boundary of `Proj.map`; the
coefficient ring may live independently. -/
@[expose] noncomputable def symmetricAlgebraProjIsoOfLinearEquiv (e : M ≃ₗ[R] N) :
    Proj (SymmetricAlgebra.homogeneousSubmodule (R := R) (M := N)) ≅
      Proj (SymmetricAlgebra.homogeneousSubmodule (R := R) (M := M)) :=
  projIsoOfInverseGradedRingHom
    (SymmetricAlgebra.gradedMap e.toLinearMap).toGradedRingHom
    (SymmetricAlgebra.gradedMap e.symm.toLinearMap).toGradedRingHom
    (symmetricAlgebraGradedMap_comp_symm e)
    (symmetricAlgebraGradedMap_symm_comp e)

end LinearEquivScheme
end
end ProjectiveSpace
end
