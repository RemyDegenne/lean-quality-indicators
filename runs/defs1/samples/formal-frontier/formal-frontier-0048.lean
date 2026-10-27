public section

open Function Set

universe u

namespace ModuleCat.FiniteProjective

variable {R : Type u} [CommRing R]

/-- The idempotent cutting out the threshold set `rankClopen f i`. -/
noncomputable def rankIdempotent
    (f : LocallyConstant (PrimeSpectrum R) ℕ) (i : Fin (rankBound f)) : R :=
  (PrimeSpectrum.isIdempotentElemEquivClopens (R := R)).symm (rankClopen f i)

end ModuleCat.FiniteProjective
end
