namespace P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 8000000

set_option maxHeartbeats 6400000

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

p2m_reactivate

section

variable {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R) [Nontrivial (R ⧸ I)]

p2m_open

p2m_reactivate

p2m_reactivate

section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

section

namespace IsDedekindDomain

namespace HeightOneSpectrum

p2m_open

p2m_reactivate

variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDedekindDomain A] (v : HeightOneSpectrum A)

p2m_open_scoped

local notation "vK" => (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)

scoped instance : Valuation.IsRankOneDiscrete vK where
  exists_generator_lt_one' := by
    have h : (v.valuation K).IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' (valuation K v)
    exact ⟨h.generator, by rw [h.generator_zpowers_eq_valueGroup, adicCompletion_valueGroup_eq],
      h.generator_lt_one⟩

scoped instance : (v.completionIdeal K).LiesOver v.asIdeal where
  «over» := by
    rw [Ideal.under_def]
    ext x
    simp only [Ideal.mem_comap, mem_completionIdeal_iff, algebraMap_completionIntegers,
      valuedAdicCompletion_eq_valuation, valuation_lt_one_iff_mem]

open _root_.IsLocalRing _root_.P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsLocalRing in

noncomputable def ResidueFieldEquivCompletionResidueField :
    A ⧸ v.asIdeal ≃+* ResidueField (v.adicCompletionIntegers K) :=
  RingEquiv.ofBijective (ResidueFieldToCompletionResidueField K v)
    ⟨s18_resField_inj K v, s18_resField_surj K v⟩

end HeightOneSpectrum
end IsDedekindDomain
end
end
end
end
end
end P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three
