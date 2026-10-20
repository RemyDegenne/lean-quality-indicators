@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace Zeta32.Analytic.EnergyI

noncomputable section

theorem gtil_eq (c : ℝ) :
    gtil c = 1/3 + (4/3) * (Ici (1:ℝ)).indicator 1 c - (1/3) * (Ici (5:ℝ)).indicator 1 c := by
  unfold gtil
  by_cases h1 : c < 1
  · have h5 : c < 5 := by linarith
    simp [h1, show ¬ (1:ℝ) ≤ c by linarith, show ¬ (5:ℝ) ≤ c by linarith, Set.indicator]
  · by_cases h5 : c < 5
    · simp [h1, h5, show (1:ℝ) ≤ c by linarith, show ¬ (5:ℝ) ≤ c by linarith, Set.indicator];
      norm_num
    · simp [h1, h5, show (1:ℝ) ≤ c by linarith, show (5:ℝ) ≤ c by linarith, Set.indicator]

end
end Zeta32.Analytic.EnergyI
end
