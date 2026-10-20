public section

open scoped DirectSum

namespace SymmetricAlgebra

universe u v

variable {R : Type u} {M : Type v}

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

variable (R M)

variable {R M}

section Map

universe w

variable {N : Type w} [AddCommMonoid N] [Module R N]

/-- The functorial map on symmetric algebras, bundled as a degree-preserving algebra map. -/
@[expose]
def gradedMap (f : M →ₗ[R] N) :
    homogeneousSubmodule (R := R) (M := M) →ₐᵍ[R]
      homogeneousSubmodule (R := R) (M := N) where
  toAlgHom := map f
  map_mem := map_mem_homogeneousSubmodule f

end Map
end SymmetricAlgebra
end
