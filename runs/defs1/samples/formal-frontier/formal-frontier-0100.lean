public section

open Function Set

universe u v

namespace Module

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Projective R M]

/-- The idempotent corresponding to a rank fiber. -/
noncomputable def rankFiberIdempotent (i : rankFiberIndex R M) : R :=
  (PrimeSpectrum.isIdempotentElemEquivClopens (R := R)).symm
    (rankFiberClopen R M i)

end Module
end
