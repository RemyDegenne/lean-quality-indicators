@[expose] public section

open CategoryTheory

open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry

universe u v

namespace FiniteGroupFunctions

variable {K : Type u} {Γ : Type v} {R S : Type*}

variable [CommRing K] [Fintype Γ]

namespace Points

/-- The idempotent whose basic open in `PrimeSpectrum R` is the fibre of a locally
constant function over `g`. -/
noncomputable def idempotentOfLocallyConstant [CommRing R]
    (f : LocallyConstant (PrimeSpectrum R) Γ) (g : Γ) : R :=
  (PrimeSpectrum.isIdempotentElemEquivClopens.symm (fiberClopen f g)).1

end Points
end FiniteGroupFunctions
end AlgebraicGeometry
end
