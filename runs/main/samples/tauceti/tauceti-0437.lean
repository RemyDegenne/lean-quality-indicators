public section

namespace TauCeti

open Bornology Filter Metric Set Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace F]

theorem tendsto_nhdsNE_of_tendsto_radial_of_tendsto_diam_image_sphere
    {u : E → F} {a v : E} {q : F} (hv : ‖v‖ = 1)
    (hr : Tendsto (fun t : ℝ ↦ u (a + t • v)) (𝓝[>] 0) (𝓝 q))
    (hb : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsBounded (u '' sphere a t))
    (hd : Tendsto (fun t ↦ diam (u '' sphere a t)) (𝓝[>] 0) (𝓝 0)) :
    Tendsto u (𝓝[≠] a) (𝓝 q) := by
  have hρ := tendsto_norm_sub_self_nhdsNE a
  have hrad := (tendsto_iff_dist_tendsto_zero.mp hr).comp hρ
  have hdiam := hd.comp hρ
  apply tendsto_iff_dist_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) ?_
    (by simpa only [zero_add] using hdiam.add hrad)
  filter_upwards [hρ.eventually hb] with x hx
  have hxs : x ∈ sphere a ‖x - a‖ := by simp
  have hrs : a + ‖x - a‖ • v ∈ sphere a ‖x - a‖ := by
    simp [norm_smul, hv]
  exact (dist_triangle _ _ _).trans
    (add_le_add (dist_le_diam_of_mem hx (mem_image_of_mem u hxs)
      (mem_image_of_mem u hrs)) le_rfl)

end TauCeti
end
