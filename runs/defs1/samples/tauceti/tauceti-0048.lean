public section

noncomputable section

open CategoryTheory Finsupp

universe u v

namespace TauCeti

variable {ι : Type u} [LinearOrder ι]

variable (K : _root_.AbstractSimplicialComplex ι)

/-- Ordered simplicial `n`-chains with coefficients in `R`: finite linear combinations of the
`n`-dimensional faces, oriented by their increasing vertex enumerations. -/
abbrev OrderedSimplicialChain (R : Type v) [Semiring R] (n : ℕ) :=
  _root_.AbstractSimplicialComplex.RealizationCell K n →₀ R

end TauCeti
end
end
