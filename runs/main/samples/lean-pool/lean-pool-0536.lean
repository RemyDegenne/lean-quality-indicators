public section

noncomputable section

open Set Filter Metric

open scoped ContDiff Topology

namespace NavierStokesAndEuler.SmoothCutoff

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {E}

theorem cutoff_eq_zero {R : ℝ} (hR : 0 < R) {x : E} (hx : 2 * R ≤ ‖x‖) :
    cutoff E R x = 0 := by
  apply baseCutoff_eq_zero
  rw [norm_inv_smul hR, le_div_iff₀ hR]
  exact hx

end NavierStokesAndEuler.SmoothCutoff
end
end
