public section

namespace Real

open Filter Topology

theorem tendsto_log_one_div_sub_atTop (a : ℝ) :
    Tendsto (fun s : ℝ ↦ Real.log (1 / (s - a))) (𝓝[>] a) atTop := by
  refine Real.tendsto_log_atTop.comp ?_
  have h1 : Tendsto (fun s : ℝ ↦ s - a) (𝓝[>] a) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (((continuous_sub_right a).tendsto' a 0 (by ring)).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun s hs ↦ by
        simp only [Set.mem_Ioi] at hs ⊢
        linarith)
  simpa only [one_div, Pi.inv_def] using h1.inv_tendsto_nhdsGT_zero

end Real
end
