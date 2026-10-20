public section

open Function Set

universe u

namespace ModuleCat.FiniteProjective

variable {R : Type u} [CommRing R]

/-- The complementary finite projective module in the finite-free realization
of a locally constant stalk-rank function. -/
noncomputable def complementOfLocallyConstantRank (R : Type u) [CommRing R]
    (f : LocallyConstant (PrimeSpectrum R) ℕ) : ModuleCat.FiniteProjective R := by
  let _ : Module.Finite R (rankComplement R f) := rankComplementFinite f
  let _ : Module.Projective R (rankComplement R f) := rankComplementProjective f
  exact ModuleCat.FiniteProjective.of R (rankComplement R f)

end ModuleCat.FiniteProjective
end
