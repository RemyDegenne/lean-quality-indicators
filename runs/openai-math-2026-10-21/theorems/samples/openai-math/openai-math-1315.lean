namespace OAI

noncomputable section

namespace ZeroKey

section

open MeasureTheory ProbabilityTheory Set Function unitInterval

open scoped ENNReal

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal

universe v3643_0

open MeasureTheory ProbabilityTheory Function Set

section

universe v3698_0

lemma indep_condIndep_bot {Ω : Type v3698_0} {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {A B : MeasurableSpace Ω} (hA : A ≤ mΩ) (hB : B ≤ mΩ) (h : Indep A B P) :
    CondIndep ⊥ A B bot_le P := by
  rw [condIndep_iff _ _ _ _ hA hB]
  intro s t hs ht
  have hmul := (h.indepSet_of_measurableSet hs ht).measure_inter_eq_mul
  simp only [condExp_bot, integral_indicator (hA s hs), integral_indicator (hB t ht),
    integral_indicator ((hA s hs).inter (hB t ht)), integral_const,
    smul_eq_mul, mul_one]
  exact Filter.Eventually.of_forall fun _ => by
    simpa only [Measure.real, Measure.restrict_apply_univ, Pi.mul_apply, ENNReal.toReal_mul] using congrArg ENNReal.toReal hmul

end
end
end ZeroKey
end
end OAI
