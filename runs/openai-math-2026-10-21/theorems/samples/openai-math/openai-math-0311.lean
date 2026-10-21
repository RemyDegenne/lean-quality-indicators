namespace OAI

section

noncomputable section

namespace UniformKServer.SideTracker

open scoped Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem right_derivative_nonneg {f : ℝ → ℝ} {d δ : ℝ} (hδ : 0 < δ)
    (hf : HasDerivAt f d 0) (hmin : ∀ s, 0 < s → s < δ → f 0 ≤ f s) : 0 ≤ d := by
  apply ge_of_tendsto hf.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)] with s hs hsδ
  simp only [Set.mem_Ioi, Set.mem_Iio] at hs hsδ
  simp only [zero_add, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr hs.le) (sub_nonneg.mpr (hmin s hs hsδ))

end UniformKServer.SideTracker
end
end
end OAI
