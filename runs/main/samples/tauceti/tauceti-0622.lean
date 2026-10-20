public section

noncomputable section

open IsDedekindDomain

open scoped WithZero AdicCompletionIntegers

open UniformSpace WithZeroTopology

open HeightOneSpectrum.adicCompletion

namespace TauCeti.Place

variable (k F : Type*) {R : Type*} [Field k] [Field F] [CommRing R]
  [IsDedekindDomain R] [Algebra k R] [Algebra R F] [IsFractionRing R F] [Algebra k F]
  [IsScalarTower k R F] (p : HeightOneSpectrum R)

@[simp]
theorem completionEquivAdicCompletion_mem_integers_iff (x : (ofPrime k F p).Completion) :
    completionEquivAdicCompletion k F p x ∈ p.adicCompletionIntegers F ↔
      x ∈ (ofPrime k F p).completionPlace.integers := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, valuation_completionEquivAdicCompletion,
    mem_integers_iff]

end TauCeti.Place
end
end
