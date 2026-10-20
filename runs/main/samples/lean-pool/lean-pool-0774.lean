@[expose] public section

namespace Nivat.Dynamics

open Filter Set

open scoped Topology InnerProductSpace

theorem eventually_norm_add_lt_of_normal_tendsto (p : ℕ → RealPlane) (ν z : RealPlane)
    (hp : ∀ n, p n ≠ 0) (hr : Tendsto (fun n => ‖p n‖) atTop atTop)
    (hν : Tendsto (fun n => ‖p n‖⁻¹ • p n) atTop (𝓝 ν))
    (hz : ⟪ν, z⟫_ℝ < 0) : ∀ᶠ n in atTop, ‖p n + z‖ < ‖p n‖ := by
  have hinv : Tendsto (fun n => ‖p n‖⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hr
  have hinner : Tendsto (fun n => ⟪‖p n‖⁻¹ • p n, z⟫_ℝ) atTop (𝓝 ⟪ν, z⟫_ℝ) :=
    hν.inner tendsto_const_nhds
  have hg : Tendsto
      (fun n => 2 * ⟪‖p n‖⁻¹ • p n, z⟫_ℝ + ‖z‖ ^ 2 * ‖p n‖⁻¹)
      atTop (𝓝 (2 * ⟪ν, z⟫_ℝ)) := by
    simpa using (tendsto_const_nhds.mul hinner).add (tendsto_const_nhds.mul hinv)
  have he := hg.eventually_lt_const (by linarith : 2 * ⟪ν, z⟫_ℝ < 0)
  filter_upwards [he] with n hn
  have hr0 : 0 < ‖p n‖ := norm_pos_iff.mpr (hp n)
  have hn' : (2 * ⟪p n, z⟫_ℝ + ‖z‖ ^ 2) / ‖p n‖ < 0 := by
    simpa [real_inner_smul_left, div_eq_mul_inv, add_mul, mul_assoc, mul_left_comm,
      mul_comm] using hn
  have hnum : 2 * ⟪p n, z⟫_ℝ + ‖z‖ ^ 2 < 0 := by simpa using (div_lt_iff₀ hr0).mp hn'
  have hs := norm_add_sq_real (p n) z
  nlinarith [norm_nonneg (p n + z), norm_nonneg (p n)]

end Nivat.Dynamics
end
