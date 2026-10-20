public section

open Function Set

open CategoryTheory

universe u v w

namespace Module

variable {R : Type u} [CommRing R]

section CanonicalRealization

/-- The value of the rank on a nonempty rank fiber of the canonical
realization of `f`. -/
noncomputable abbrev locallyConstantRankFiberRank
    (f : LocallyConstant (PrimeSpectrum R) ℕ)
    (j : locallyConstantRankFiberIndex f) : ℕ :=
  rankFiberRank R (ModuleCat.FiniteProjective.ofLocallyConstantRank R f) j

end CanonicalRealization
end Module
end
