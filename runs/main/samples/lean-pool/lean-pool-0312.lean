@[expose] public section

open MeasureTheory Set

namespace QuadraticCarleson

theorem integral_le_four_mul_succ_of_le_lowDecayMajorant
    (F : ℝ → ℝ) (A ℓ z : ℝ) (B : ℕ)
    (hA : 0 ≤ A) (hℓ : 0 < ℓ)
    (hFmeas : AEStronglyMeasurable F
      (volume.restrict (Icc (z - ℓ) (z + ℓ))ᶜ))
    (hFnonneg : ∀ x ∉ Icc (z - ℓ) (z + ℓ), 0 ≤ F x)
    (hFbound : ∀ x ∉ Icc (z - ℓ) (z + ℓ),
      F x ≤ A * lowDecayMajorant ((2 : ℝ) ^ (2 * B)) ℓ z x) :
    ∫ x in (Icc (z - ℓ) (z + ℓ))ᶜ, F x ≤
      4 * (B + 1 : ℝ) * A := by
  have hD : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * B) := one_le_pow₀ (by norm_num)
  have hdecay := integrableOn_lowDecayMajorant_compl
    ((2 : ℝ) ^ (2 * B)) ℓ z hD hℓ
  have hscaled : IntegrableOn
      (fun x ↦ A * lowDecayMajorant ((2 : ℝ) ^ (2 * B)) ℓ z x)
      (Icc (z - ℓ) (z + ℓ))ᶜ := hdecay.const_mul A
  have hcompl : MeasurableSet (Icc (z - ℓ) (z + ℓ))ᶜ := measurableSet_Icc.compl
  have hFint : IntegrableOn F (Icc (z - ℓ) (z + ℓ))ᶜ := by
    apply hscaled.mono' hFmeas
    filter_upwards [ae_restrict_mem hcompl] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnonneg x hx)]
    exact hFbound x hx
  calc
    (∫ x in (Icc (z - ℓ) (z + ℓ))ᶜ, F x) ≤
        ∫ x in (Icc (z - ℓ) (z + ℓ))ᶜ,
          A * lowDecayMajorant ((2 : ℝ) ^ (2 * B)) ℓ z x := by
      apply integral_mono_ae hFint hscaled
      filter_upwards [ae_restrict_mem hcompl] with x hx
      exact hFbound x hx
    _ = A * ∫ x in (Icc (z - ℓ) (z + ℓ))ᶜ,
          lowDecayMajorant ((2 : ℝ) ^ (2 * B)) ℓ z x := by
      rw [integral_const_mul]
    _ ≤ A * (4 * (B + 1 : ℝ)) := mul_le_mul_of_nonneg_left
      (integral_lowDecayMajorant_two_pow_le B ℓ z hℓ) hA
    _ = 4 * (B + 1 : ℝ) * A := by ring

end QuadraticCarleson
end
