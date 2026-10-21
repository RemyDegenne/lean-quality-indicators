namespace OAI

noncomputable section

open MeasureTheory Set

namespace Invariant233.ScalarSampling

theorem parameter_samplingAverage_eq (p : CircleParameterData) (θ : ℝ)
    (j r : ℕ) (hm : 200 ≤ p.m j) (endpoint : Bool) (x : Circle) :
    p.samplingAverage θ j r endpoint x =
      (1 / ((p.samples j r).card : ℝ)) *
        ∑ n ∈ p.samples j r, ∏ i ∈ p.block j,
          if endpoint then manuscriptEndpointKernel (p.m j) (p.coordinate i x)
            (Int.fract ((n : ℝ) * p.alpha θ i))
          else manuscriptKernel (p.m j) (p.coordinate i x)
            (Int.fract ((n : ℝ) * p.alpha θ i)) := by
  unfold CircleParameterData.samplingAverage
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.prod_congr rfl
  intro i hi
  exact parameter_orientedKernel_eq hm endpoint _
    ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

end Invariant233.ScalarSampling
end
end OAI
