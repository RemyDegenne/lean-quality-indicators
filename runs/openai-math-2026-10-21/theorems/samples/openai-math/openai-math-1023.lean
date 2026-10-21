namespace OAI

open Set MeasureTheory Metric Function

open scoped ENNReal

namespace CircleDomainRigidity

theorem ae_finite_hausdorffMeasure_mod_one_levels
    {Z : Type*} [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (L : ℝ → ℝ≥0∞) (hL : Measurable L) (hfinite : ∫⁻ t, L t < ∞)
    (A H : ℝ → Set Z)
    (hcover : ∀ t, H t ⊆ ⋃ k : ℤ, A (t + (k : ℝ)))
    (hlength : ∀ r, (μH[1] : Measure Z) (A r) ≤ L r) :
    ∀ᵐ t ∂volume.restrict (Ico (0 : ℝ) 1), (μH[1] : Measure Z) (H t) < ∞ := by
  filter_upwards [ae_finite_periodizedLevelLength L hL hfinite] with t ht
  apply lt_of_le_of_lt _ ht
  calc
    (μH[1] : Measure Z) (H t) ≤ (μH[1] : Measure Z) (⋃ k : ℤ, A (t + (k : ℝ))) :=
      measure_mono (hcover t)
    _ ≤ ∑' k : ℤ, (μH[1] : Measure Z) (A (t + (k : ℝ))) := measure_iUnion_le _
    _ ≤ periodizedLevelLength L t := ENNReal.tsum_le_tsum (fun k => hlength (t + (k : ℝ)))

end CircleDomainRigidity
end OAI
