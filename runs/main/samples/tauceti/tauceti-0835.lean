public section

noncomputable section

open MeasureTheory InformationTheory Set

open scoped ENNReal

namespace TauCeti

variable {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
  {R P : Measure Ω} {e : Ω → X × Y} {π : Measure (X × Y)} {μ : Measure X} {ν : Measure Y}
  {a : ℝ≥0∞}

theorem rnDeriv_ae_eq_rnDeriv_map_comp_of_klDiv_eq_dynamicSchroedingerValue [IsFiniteMeasure μ]
    [IsFiniteMeasure R] (he : Measurable e) (hP : IsCoupling (P.map e) μ ν)
    (hPval : klDiv P R = dynamicSchroedingerValue R e μ ν)
    (h : dynamicSchroedingerValue R e μ ν ≠ ∞) :
    P.rnDeriv R =ᵐ[R] fun ω ↦ (P.map e).rnDeriv (R.map e) (e ω) := by
  have hfit := ((klDiv_eq_dynamicSchroedingerValue_iff he hP h).1 hPval).2
  have hdens := Measure.rnDeriv_fitLaw (π := R) (μ := P.map e) he
  rwa [← hfit] at hdens

end TauCeti
end
end
