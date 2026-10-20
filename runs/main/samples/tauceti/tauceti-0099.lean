public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal NNReal

namespace TauCeti

universe u

variable {X : Type u} [MeasurableSpace X] {p q : ℝ≥0∞} {a : ℝ≥0∞}

section NormedMoment

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]

variable [OpensMeasurableSpace E] [SecondCountableTopology E]

theorem integrable_norm_sub_sq_of_hasFiniteMoment {π : Measure (E × E)} [IsFiniteMeasure π]
    (h₁ : HasFiniteMoment 2 π.fst) (h₂ : HasFiniteMoment 2 π.snd) :
    Integrable (fun z : E × E ↦ ‖z.1 - z.2‖ ^ 2) π := by
  rw [Measure.fst] at h₁
  rw [Measure.snd] at h₂
  exact (memLp_two_iff_integrable_sq_norm (by fun_prop)).1 <|
    (memLp_of_hasFiniteMoment_map measurable_fst h₁).sub
      (memLp_of_hasFiniteMoment_map measurable_snd h₂)

end NormedMoment
end TauCeti
end
end
