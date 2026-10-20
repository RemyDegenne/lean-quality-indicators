public section

noncomputable section

open Set Filter Metric

open scoped ContDiff Topology

namespace NavierStokesAndEuler.SmoothCutoff

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {E}

theorem cutoff_eq_one {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R) :
    cutoff E R x = 1 := by
  apply baseCutoff_eq_one
  rw [norm_inv_smul hR, div_le_one hR]
  exact hx

end NavierStokesAndEuler.SmoothCutoff
end
end
