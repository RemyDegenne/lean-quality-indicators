public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

variable {m Ω q : ℝ}

@[simp]
theorem integrableExpSet_id_nakagamiMeasure (m Ω : ℝ) :
    integrableExpSet id (nakagamiMeasure m Ω) = univ := by
  ext t
  simp only [integrableExpSet, id_eq, mem_ofPred_eq, mem_univ, iff_true]
  exact integrable_exp_mul_id_nakagamiMeasure m Ω t

end TauCeti.Probability
end
end
