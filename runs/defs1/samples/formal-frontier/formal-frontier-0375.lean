public section

open Function Set

universe u

namespace ModuleCat.FiniteProjective

variable {R : Type u} [CommRing R]

/-- The clopen threshold set on which the prescribed rank is greater than `i`. -/
def rankClopen (f : LocallyConstant (PrimeSpectrum R) ℕ)
    (i : Fin (rankBound f)) : TopologicalSpace.Clopens (PrimeSpectrum R) :=
  ⟨{p | i.1 < f p}, (isClopen_discrete _).preimage f.continuous⟩

end ModuleCat.FiniteProjective
end
