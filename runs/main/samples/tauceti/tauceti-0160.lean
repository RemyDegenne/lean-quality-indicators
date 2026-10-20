public section

noncomputable section

namespace TauCeti

open InnerProductSpace MeasureTheory Metric Set Filter

open scoped RealInnerProductSpace Topology

variable {n : ℕ}

@[simp] theorem ballPoissonIntegral_zero (x : EuclideanSpace ℝ (Fin n)) :
    ballPoissonIntegral (fun _ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ↦ 0) x = 0 := by
  simp [ballPoissonIntegral_def]

end TauCeti
end
end
