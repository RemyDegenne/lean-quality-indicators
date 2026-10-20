open Metric Set Function Filter

open scoped Topology ComplexConjugate

namespace Complex

public section

section DimOne

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {R R₁ R₂ : ℝ} {f : ℂ → E}
  {c z z₀ : ℂ}

theorem norm_dslope_le_div_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R₁))
    (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂)) (hz : z ∈ ball c R₁) :
    ‖dslope f c z‖ ≤ R₂ / R₁ := by
  rcases eq_or_ne z c with rfl | hne
  · simpa using norm_deriv_le_div_of_mapsTo_ball hd h_maps (by simpa using hz)
  · rw [dslope_of_ne _ hne, slope_def_module, norm_smul, norm_inv, ← dist_eq_norm_sub,
      ← dist_eq_norm_sub, ← div_eq_inv_mul, div_le_iff₀]
    · exact dist_le_div_mul_dist_of_mapsTo_ball hd h_maps hz
    · simpa

end DimOne
end
end Complex
