@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section4

theorem iterate_physical_stream_kernel_gains {a e γ κ c L F : ℝ}
    (ha : 0 ≤ a) (he : 0 < e) (hκ : 0 < κ) (hc : 0 < c)
    (hL : 0 < L) (hFp : 0 < F)
    (hlower : c * (a * e ^ (2 + γ)) ≤ κ)
    (hF : F = e ^ (1 + γ / 2) * L) :
    ((24 * (2 * ((2 : ℝ) ^ 19 * a) / L ^ 2)) / κ ≤
      (48 * (2 : ℝ) ^ 19 / c) / F ^ 2) ∧
    ((24 * (16 / κ * (32 * a * e ^ 2) ^ 2 * (2 * ((256 * e⁻¹) / L) ^ 2) ^ 2)) / κ ≤
      (24 * (16 * 32 ^ 2 * 4 * 256 ^ 4) / c ^ 2) / F ^ 4) := by
  have hr := iterate_stream_ratio_of_literal_lower he hκ hc hL hFp hlower hF
  have hu := mul_le_mul_of_nonneg_left hr (show (0 : ℝ) ≤ 48 * 2 ^ 19 by norm_num)
  have hv := iterate_quadratic_stream_scale_bound hκ ha he.ne' hL
    (show 0 ≤ (1 : ℝ) / c by positivity) hr
  have hv24 := mul_le_mul_of_nonneg_left hv (show (0 : ℝ) ≤ 24 by norm_num)
  constructor
  · convert hu using 1 <;> ring
  · convert hv24 using 1 <;> ring

end AVenhance.Infra.Section4
end
end
