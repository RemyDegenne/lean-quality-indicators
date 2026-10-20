public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

open scoped ENNReal

namespace TauCeti.Probability

variable {m Ω x c : ℝ}

variable {α : Type*} [MeasurableSpace α] {P : Measure α} {X : α → ℝ}

theorem hasLaw_nakagamiMeasure_of_hasLaw_gammaMeasure (hm : 0 < m) (hΩ : 0 < Ω)
    (hX : HasLaw X (gammaMeasure m (m / Ω)) P) :
    HasLaw (fun ω ↦ √(X ω)) (nakagamiMeasure m Ω) P := by
  rw [nakagamiMeasure_of_pos hm hΩ]
  exact (hasLaw_map (X := Real.sqrt) (by fun_prop)).fun_comp hX

end TauCeti.Probability
end
end
