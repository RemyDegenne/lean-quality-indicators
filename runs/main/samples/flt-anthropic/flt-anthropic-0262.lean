namespace P2MW.S_NumberField_TateGlobal_zetaIntegral_entire_continuation_fe_of_exists_mem_normOneIdeles_ne_one

set_option autoImplicit false

set_option maxHeartbeats 3200000

set_option maxSynthPendingDepth 3

set_option synthInstance.maxHeartbeats 1600000

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Fold_E6v20self

p2m_open

p2m_open

open scoped NNReal ENNReal Pointwise

namespace M4aD2Glue

scoped instance : tauLog.IsMulLeftInvariant := ⟨tauLog_map_mul_left⟩

scoped instance : IsFiniteMeasureOnCompacts tauLog := by
  constructor
  intro K hK
  rw [tauLog_apply hK.measurableSet]
  have hcoeh : ⇑expHomeo = expUnit := rfl
  have hKpre : IsCompact (expUnit ⁻¹' K) := by
    rw [← hcoeh]
    exact expHomeo.isCompact_preimage.mpr hK
  exact hKpre.measure_lt_top

scoped instance : tauLog.IsOpenPosMeasure := by
  constructor
  intro U hU hne
  rw [tauLog_apply hU.measurableSet]
  have hUpre : IsOpen (expUnit ⁻¹' U) := hU.preimage continuous_expUnit
  have hne2 : (expUnit ⁻¹' U).Nonempty := by
    obtain ⟨t, ht⟩ := hne
    exact ⟨Real.log ((t : ℝ≥0) : ℝ), by simp [Set.mem_preimage, expUnit_log, ht]⟩
  exact (hUpre.measure_pos MeasureTheory.volume hne2).ne'

scoped instance : tauLog.IsHaarMeasure := ⟨⟩

theorem tauLog_window_integral {c : ℂ} (hc : 0 < c.re) :
    ∫ t in {t : ℝ≥0ˣ | ((t : ℝ≥0) : ℝ) < 1},
      Complex.exp (c * Real.log ((t : ℝ≥0) : ℝ)) ∂tauLog = 1 / c := by
  have hcont : Continuous fun t : ℝ≥0ˣ => Complex.exp (c * Real.log ((t : ℝ≥0) : ℝ)) :=
    Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_logUnit))
  have hS : MeasurableSet {t : ℝ≥0ˣ | ((t : ℝ≥0) : ℝ) < 1} := by
    have hcoe : Continuous fun t : ℝ≥0ˣ => ((t : ℝ≥0) : ℝ) :=
      NNReal.continuous_coe.comp Units.isEmbedding_val₀.continuous
    exact measurableSet_lt hcoe.measurable measurable_const
  rw [tauLog, MeasureTheory.setIntegral_map hS hcont.aestronglyMeasurable
    measurable_expUnit.aemeasurable]
  rw [preimage_expUnit_lt_one]
  have hfun : ∀ x ∈ Set.Iio (0:ℝ),
      Complex.exp (c * Real.log (((expUnit x : ℝ≥0ˣ) : ℝ≥0) : ℝ)) = Complex.exp (c * x) := by
    intro x _
    rw [log_expUnit]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Iio hfun]
  rw [MeasureTheory.setIntegral_congr_set MeasureTheory.Iio_ae_eq_Iic]
  rw [integral_exp_mul_complex_Iic hc 0]
  simp

end M4aD2Glue
end Fold_E6v20self
end P2MW.S_NumberField_TateGlobal_zetaIntegral_entire_continuation_fe_of_exists_mem_normOneIdeles_ne_one
