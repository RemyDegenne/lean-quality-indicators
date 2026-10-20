public section

open scoped DirectSum

namespace SymmetricAlgebra

universe u v

variable {R : Type u} {M : Type v}

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

variable (R M)

variable {R M}

section Basis

universe w

variable {I : Type w}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The inverse basis presentation, bundled as a degree-preserving algebra map. -/
@[expose]
noncomputable def equivMvPolynomialSymmGradedHom (b : Module.Basis I R M) :
    MvPolynomial.homogeneousSubmodule I R →ₐᵍ[R]
      homogeneousSubmodule (R := R) (M := M) where
  toAlgHom := (equivMvPolynomial b).symm
  map_mem := equivMvPolynomial_symm_mem_homogeneousSubmodule b

end Basis
end SymmetricAlgebra
end
