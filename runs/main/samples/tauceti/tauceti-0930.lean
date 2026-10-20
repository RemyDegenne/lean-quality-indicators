public section

open MeasureTheory Measure Set Filter Metric Module Function

open scoped NNReal ENNReal Topology

namespace LipschitzWith

open TauCeti

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V] {f : U → V} {s : Set U}
  {K : ℝ≥0}

theorem lintegral_image_eq_lintegral_normDet_fderiv_mul (hf : LipschitzWith K f)
    (hs : MeasurableSet s) (hinj : InjOn f s) (g : V → ℝ≥0∞) :
    ∫⁻ y in f '' s, g y ∂μHE[finrank ℝ U] =
      ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).normDet * g (f x) := by
  -- Split `s` into its regular points `s ∩ G` and the rest, which contributes to neither side.
  set G := {x | DifferentiableAt ℝ f x ∧ (fderiv ℝ f x).normDet ≠ 0}
  have hG : MeasurableSet G := (measurableSet_of_differentiableAt ℝ f).inter
    (measurableSet_eq_fun (ContinuousLinearMap.continuous_normDet.measurable.comp
      (measurable_fderiv ℝ f)) measurable_const).compl
  have himage : f '' s =ᵐ[μHE[finrank ℝ U]] f '' (s ∩ G) := by
    rw [← inter_union_sdiff s G, image_union, inter_union_sdiff]
    exact union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.2 (measure_mono_null
      (image_mono (sdiff_subset_compl _ _)) hf.euclideanHausdorffMeasure_image_compl_setOf_regular))
  have hzero : ∫⁻ x in s \ G, ENNReal.ofReal (fderiv ℝ f x).normDet * g (f x) = 0 := by
    refine (setLIntegral_congr_fun_ae (hs.diff hG) ?_).trans lintegral_zero
    filter_upwards [hf.ae_differentiableAt] with x hx hxs
    rw [not_not.1 fun h => hxs.2 ⟨hx, h⟩, ENNReal.ofReal_zero, zero_mul]
  rw [setLIntegral_congr himage, ← lintegral_inter_add_sdiff _ s hG, hzero, add_zero]
  refine TauCeti.lintegral_image_eq_lintegral_normDet_fderiv_mul (hs.inter hG)
    (fun x hx => hx.2.1) (fun x hx => ?_) (hinj.mono inter_subset_left) g
  exact LinearMap.ker_eq_bot.1
    (not_not.1 fun h => hx.2.2 (LinearMap.normDet_eq_zero_iff_ker_ne_bot.2 h))

end LipschitzWith
end
