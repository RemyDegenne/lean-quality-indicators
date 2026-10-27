public section

open scoped DirectSum

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w x

variable (R : Type u) [CommRing R]

variable {L : Type v} {M : Type w} {N : Type x}

variable [LieRing L] [LieAlgebra R L]

variable [LieRing M] [LieAlgebra R M]

variable [LieRing N] [LieAlgebra R N]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The linear map between the `k`-th PBW filtration steps induced by a Lie homomorphism. -/
noncomputable def mapFiltration (f : LieHom R L M) (k : ℕ) :
    pbwFiltration R L k →ₗ[R] pbwFiltration R M k :=
  (map R f).toLinearMap.restrict fun _ hx => map_mem_pbwFiltration R f hx

end TauCeti.UniversalEnvelopingAlgebra
end
