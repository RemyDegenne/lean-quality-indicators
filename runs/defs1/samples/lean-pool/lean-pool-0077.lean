@[expose] public section

namespace NavierStokes.HolomorphicFamily

noncomputable section

open Set Filter Metric Complex MeasureTheory

open scoped Topology ContDiff Interval

open CauchyRestriction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Sampling the outer circle as a continuous map into the closed disk. -/
noncomputable def circleInput (c : ℂ) {σ : ℝ} (hσ : 0 < σ) : C(Angles, Disk c σ) where
  toFun θ := ⟨circleMap c σ θ, sphere_subset_closedBall (circleMap_mem_sphere c hσ.le θ)⟩
  continuous_toFun := ((continuous_circleMap c σ).comp continuous_subtype_val).subtype_mk _

end
end NavierStokes.HolomorphicFamily
end
