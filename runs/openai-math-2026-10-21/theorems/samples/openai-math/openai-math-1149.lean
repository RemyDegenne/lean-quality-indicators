namespace OAI

namespace KadisonKastler

open Set Filter

open scoped Topology

noncomputable section

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

theorem weightedStripContinuous_norm_le (r : C(K, ℝ))
    (hr : ∀ k, 0 ≤ r k ∧ r k ≤ 1) {z : ℂ} (hz : |z.re| ≤ 1 / 2) :
    ‖weightedStripContinuous r z‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ zero_le_one).mpr
  intro k
  rw [weightedStripContinuous_apply r (lt_of_le_of_lt hz (by norm_num))]
  exact weightedStripKernel_norm_le_one hz (hr k).1 (hr k).2

end
end KadisonKastler
end OAI
