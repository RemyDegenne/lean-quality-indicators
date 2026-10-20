@[expose] public section

open Complex MeasureTheory Set Filter Topology

open scoped Real Interval

noncomputable section

lemma integrand_bound_on_annulus
    {γ : ℝ → ℂ} {t₀ : ℝ} {C δ₀ : ℝ}
    (hr_bounded : ∀ t, 0 < |t - t₀| →
      |t - t₀| < δ₀ →
        ‖(γ t - γ t₀)⁻¹ * deriv γ t -
          (↑(t - t₀))⁻¹‖ ≤ C)
    (t : ℝ) (ht_pos : 0 < |t - t₀|)
    (ht_lt : |t - t₀| < δ₀) :
    ‖(γ t - γ t₀)⁻¹ * deriv γ t‖ ≤
      |t - t₀|⁻¹ + C := by
  have h_inv_norm : ‖(↑(t - t₀) : ℂ)⁻¹‖ =
      |t - t₀|⁻¹ := by rw [norm_inv, Complex.norm_real, Real.norm_eq_abs]
  have h := norm_sub_norm_le ((γ t - γ t₀)⁻¹ * deriv γ t) (↑(t - t₀))⁻¹
  rw [h_inv_norm] at h
  linarith [hr_bounded t ht_pos ht_lt]

end
end
