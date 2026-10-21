namespace OAI

noncomputable section

open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Classical

open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint

lemma halfPlane_realDensity_lintegral (ρ : ℂ → ℝ) (hρ : Measurable ρ)
    (f : upperHalfPlane → ℝ≥0∞) :
    (∫⁻ z, f z ∂(volume.withDensity (fun x => ENNReal.ofReal (ρ x))).comap Subtype.val) =
      ∫⁻ z in upperHalfPlane, extendHalfPlaneENN f z * ENNReal.ofReal (ρ z) := by
  calc
    _ = ∫⁻ z : upperHalfPlane, extendHalfPlaneENN f z
        ∂(volume.withDensity (fun x => ENNReal.ofReal (ρ x))).comap Subtype.val := by
      apply lintegral_congr
      intro z
      exact (extendHalfPlaneENN_apply f z).symm
    _ = ∫⁻ z in upperHalfPlane, extendHalfPlaneENN f z
        ∂volume.withDensity (fun x => ENNReal.ofReal (ρ x)) :=
      lintegral_subtype_comap isOpen_upperHalfPlane.measurableSet _
    _ = _ := by
      rw [setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable volume hρ.ennreal_ofReal _
        isOpen_upperHalfPlane.measurableSet (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
      apply lintegral_congr
      intro z
      exact mul_comm _ _

end SLEExactGauge.Multipoint
end
end OAI
