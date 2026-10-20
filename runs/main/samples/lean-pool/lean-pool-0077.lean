@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace MRRW

section

open Filter Topology

open scoped Topology

theorem hasDerivAt_mul_continuous_zero
    (g : ℝ → ℝ) (hg : ContinuousAt g 0) (hgzero : g 0 = 0) :
    HasDerivAt (fun r : ℝ => r * g r) 0 0 := by
  apply (hasDerivAt_iff_tendsto_slope_zero).2
  have htend : Tendsto g (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [hgzero] using hg.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  have hquotient :
      Tendsto (fun r : ℝ => r⁻¹ * (r * g r))
        (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    refine (tendsto_congr' ?_).2 htend
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hrzero : r ≠ 0 := by simpa only [ne_eq, Set.mem_compl_iff, Set.mem_singleton_iff] using hr
    field_simp [hrzero]
  simpa only [zero_add, zero_mul, sub_zero, smul_eq_mul] using hquotient

end
end MRRW
end MetricCodes
end MetricCodesNoncomputable
end
