@[expose] public section

open CategoryTheory

open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry

universe u v

namespace FiniteGroupFunctions

variable {K : Type u} {Γ : Type v} {R S : Type*}

variable [CommRing K] [Fintype Γ]

namespace Points

/-- Locally constant functions on `PrimeSpectrum R` with finite codomain `Γ` are
equivalent to `K`-algebra homomorphisms from the finite function algebra on `Γ`.
The construction uses Mathlib's idempotent–clopen correspondence and complete
orthogonal idempotents. -/
noncomputable def locallyConstantEquivAlgHom [CommRing R] [Algebra K R] :
    LocallyConstant (PrimeSpectrum R) Γ ≃
      (FiniteGroupFunctions K Γ →ₐ[K] R) :=
  locallyConstantEquivIdempotentPartitions.trans algHomEquivIdempotentPartitions.symm

end Points
end FiniteGroupFunctions
end AlgebraicGeometry
end
