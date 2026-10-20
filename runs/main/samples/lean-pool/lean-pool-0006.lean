@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section4

theorem iterate_corrected_material_unnormalized {C C₀ q : ℝ}
    (hC : 0 ≤ C) (hC₀ : 0 < C₀) (hq : 0 < q) (hsmall : C₀ * q ≤ 1)
    {i : ℕ} (hi : 2 ≤ i) :
    C * (q ^ 2 * iterateAmplitude (C₀ * q) (i - 1) ^ 2 +
      q * iterateAmplitude (C₀ * q) (i - 1) ^ 2 +
      q ^ 2 * iterateAmplitude (C₀ * q) (i - 2) ^ 2) ≤
      (C / C₀ + 2 * C / C₀ ^ 2) * iterateAmplitude (C₀ * q) i ^ 2 := by
  have ha := iterateAmplitudeSq_pos (mul_pos hC₀ hq) i
  have hb := iterate_corrected_material_remainder_bound hC hC₀ hq hsmall hi
  have he : C * (q ^ 2 * iterateAmplitudeSq (C₀ * q) (i - 1) /
      iterateAmplitudeSq (C₀ * q) i) +
      C * (q * iterateAmplitudeSq (C₀ * q) (i - 1) /
      iterateAmplitudeSq (C₀ * q) i) +
      C * (q ^ 2 * iterateAmplitudeSq (C₀ * q) (i - 2) /
      iterateAmplitudeSq (C₀ * q) i) =
      C * (q ^ 2 * iterateAmplitudeSq (C₀ * q) (i - 1) +
      q * iterateAmplitudeSq (C₀ * q) (i - 1) +
      q ^ 2 * iterateAmplitudeSq (C₀ * q) (i - 2)) /
      iterateAmplitudeSq (C₀ * q) i := by ring
  rw [he] at hb
  have h := (div_le_iff₀ ha).mp hb
  simpa only [← iterateAmplitude_square (mul_pos hC₀ hq).le] using h

end AVenhance.Infra.Section4
end
end
