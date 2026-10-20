@[expose] public section

noncomputable section

open Set Filter MeasureTheory MeasureTheory.Measure TopologicalSpace Metric

open ENNReal (ofReal)

open scoped ENNReal NNReal Topology

namespace Real

variable {ι : Type*} [Fintype ι]

@[simp]
nonrec theorem volume_pi_closedBall (a : ι → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.closedBall a r) = ENNReal.ofReal ((2 * r) ^ Fintype.card ι) := by
  simp only [MeasureTheory.volume_pi_closedBall a hr, volume_closedBall, Finset.prod_const]
  exact (ENNReal.ofReal_pow (mul_nonneg zero_le_two hr) _).symm

end Real
end
end
