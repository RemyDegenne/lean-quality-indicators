public section

open Set CKN.Foundation.Parabolic

noncomputable section

namespace ESS

theorem blowupPressure_eq_riesz_add_remainder_of_mem
    (x₀ : Vec3) (t₀ r : ℝ) (p p₁ : ParabolicPoint → ℝ)
    (z : ParabolicPoint) (hz : z ∈ blowupDomain x₀ t₀ r) :
    blowupPressure x₀ t₀ r p z =
      blowupRieszPressure x₀ t₀ r p₁ z +
        blowupPressureRemainder x₀ t₀ r p p₁ z := by
  let y := parabolicTranslate x₀ t₀ (parabolicScale r z)
  have hy : y ∈ goodPointDomain := hz
  have htime : y.2 ∈ Ioo (-1 : ℝ) 0 := hy.2
  rw [blowupPressure_eq_of_mem x₀ t₀ r p z hz]
  simp only [blowupRieszPressure, blowupPressureRemainder,
    parabolicRescalePressure, blowupTimeExtendedPressure]
  rw [show parabolicTranslate x₀ t₀ (parabolicScale r z) = y from rfl,
    Set.indicator_of_mem htime, Set.indicator_of_mem hy]
  have hEta : ((y.1, y.2) : ParabolicPoint) = y := by
    cases y
    rfl
  rw [hEta]
  ring

end ESS
end
end
