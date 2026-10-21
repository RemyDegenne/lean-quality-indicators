namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Topology NNReal

namespace Problem367

@[simp] theorem infiniteGibbsSpinMean_zero {d : ℕ} (beta : ℝ)
    (v : TreeVertex d) : infiniteGibbsSpinMean beta v (fun _ => 0) = 0 := by
  have hlim : Tendsto (fun n => finiteGibbsSpinMean beta v n (fun _ => 0))
      atTop (𝓝 0) := by simp
  rw [infiniteGibbsSpinMean, hlim.limUnder_eq]
  norm_num

end Problem367
end
end OAI
