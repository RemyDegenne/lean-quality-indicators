@[expose] public section

open CategoryTheory

open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry

universe u v

namespace FiniteGroupFunctions

variable {K : Type u} {Γ : Type v} {R S : Type*}

variable [CommRing K] [Fintype Γ]

namespace Points

omit [Fintype Γ] in
theorem idempotentOfLocallyConstant_isIdempotent [CommRing R]
    (f : LocallyConstant (PrimeSpectrum R) Γ) (g : Γ) :
    IsIdempotentElem (idempotentOfLocallyConstant f g) :=
  (PrimeSpectrum.isIdempotentElemEquivClopens.symm (fiberClopen f g)).2

end Points
end FiniteGroupFunctions
end AlgebraicGeometry
end
