set_option warningAsError true

@[expose] public section

open Complex Set MeasureTheory

open scoped Real

universe u

variable {n : ℕ} {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem torusIntegral_prod_inv_normalized (f : (Fin n → ℂ) → F)
    (c z : Fin n → ℂ) (R : Fin n → ℝ) :
    ((2 * (π : ℂ) * I) ^ n)⁻¹ •
        torusIntegral (fun w => (∏ i, (w i - z i)⁻¹) • f w) c R =
      (((2 * π : ℝ) ^ n : ℝ) : ℂ)⁻¹ •
        ∫ θ : Fin n → ℝ in Icc (0 : Fin n → ℝ) (fun _ => 2 * π),
          (∏ i, (torusMap c R θ i - c i) / (torusMap c R θ i - z i)) •
            f (torusMap c R θ) := by
  rw [torusIntegral_prod_inv, smul_smul, normalized_factor]

end
