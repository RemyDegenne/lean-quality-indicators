public section

noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace TauCeti.Probability

variable {a c s q : ℝ}

@[simp]
theorem integrable_id_generalizedGammaMeasure_iff
    (ha : 0 < a) (hc : c ≠ 0) (hs : 0 < s) :
    Integrable id (generalizedGammaMeasure a c s) ↔ 0 < a + c⁻¹ := by
  simpa only [Function.id_def, pow_one, Nat.cast_one, one_div] using
    integrable_pow_generalizedGammaMeasure_iff ha hc hs 1

end TauCeti.Probability
end
end
