public section

noncomputable section

open MeasureTheory ProbabilityTheory unitInterval

open scoped ENNReal NNReal

namespace TauCeti

namespace Probability

theorem coinKernel_apply_true (p : I) :
    (coinKernel p : Measure Bool) {true} = (toNNReal p : ℝ≥0∞) := by
  rw [coinKernel_toMeasure]
  exact bernoulliMeasure_apply_of_mem_of_notMem p (measurableSet_singleton _) rfl (by simp)

end Probability
end TauCeti
end
end
