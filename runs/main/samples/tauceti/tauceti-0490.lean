public section

namespace TauCeti

open Complex Metric MeasureTheory Set Filter Topology

open scoped ENNReal NNReal Real

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

variable {J : V → V →L[ℝ] V} {W K : Set V} {u : ℂ → V} {z₀ : ℂ} {R : ℝ}

theorem tendsto_diam_image_sphere_nhdsGT_zero
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) (hR : 0 < R)
    (hu : ContDiffOn ℝ 3 u (ball z₀ R \ {z₀}))
    (hCR : ∀ z ∈ ball z₀ R \ {z₀}, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (huK : MapsTo u (ball z₀ R \ {z₀}) K)
    (hE : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R)) :
    Tendsto (fun ρ ↦ diam (u '' sphere z₀ ρ)) (𝓝[>] 0) (𝓝 0) := by
  refine tendsto_diam_image_sphere_nhdsGT_zero_of_tendsto ?_
    (tendsto_norm_sub_mul_norm_fderiv_nhdsNE hW hJ hK hKW hJsq hR hu hCR huK hE)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds z₀ hR)] with z hz hzR
  exact (hu.contDiffAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hzR, hz⟩)).differentiableAt
    (by norm_num)

end TauCeti
end
