open Real MeasureTheory Set Filter Topology

namespace LeanPolyLog.Arctan

public theorem integral_log_mul_Lir_two_neg_div_one_add_sq :
    ∫ x in (0 : ℝ)..1, log x * Lir 2 (-x) / (1 + x ^ 2) = π ^ 2 * G / 48 := by
  set μ : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod volume with hμ
  set S : Set (ℝ × ℝ) := Ioc 0 1 ×ˢ Ioc 0 1 with hS
  set f : ℝ × ℝ → ℝ := fun z ↦ z.1 / ((1 + z.1 ^ 2) * (1 + z.1 * z.2)) * (log z.1 * log z.2)
    with hf
  set a : ℝ → ℝ := fun t ↦ t * log t / (1 + t ^ 2) with ha
  set b : ℝ → ℝ := fun t ↦ log t / (1 + t ^ 2) with hb
  have hlog : Integrable (fun t : ℝ ↦ log t) (volume.restrict (Ioc 0 1)) :=
    intervalIntegral.intervalIntegrable_log'.1
  have ia : Integrable a (volume.restrict (Ioc 0 1)) :=
    (continuous_mul_log.div (by fun_prop) fun t ↦ by positivity).integrableOn_Ioc
  have ib : Integrable b (volume.restrict (Ioc 0 1)) := by
    have h := intervalIntegral.intervalIntegrable_log'.mul_continuousOn
      (g := fun y : ℝ ↦ (1 + y ^ 2)⁻¹) (a := 0) (b := 1) continuous_inv_one_add_sq.continuousOn
    have h' : IntegrableOn (fun t : ℝ ↦ log t / (1 + t ^ 2)) (Ioc 0 1) := by
      simpa only [div_eq_mul_inv] using h.1
    exact h'
  -- `f` is integrable on the square, dominated by `|log x| |log y|`
  have hfi : IntegrableOn f S μ := by
    rw [IntegrableOn, hμ, hS, ← Measure.prod_restrict]
    refine (hlog.norm.mul_prod hlog.norm).mono' ?_ ?_
    · exact (by fun_prop : Measurable f).aestronglyMeasurable
    · rw [Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with z hz
      obtain ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ := hz
      simp only [hf, norm_mul]
      refine mul_le_of_le_one_left (by positivity) ?_
      rw [Real.norm_of_nonneg (by positivity), div_le_one (by positivity)]
      have hxy := mul_pos hx0 hy0
      nlinarith [sq_nonneg z.1, mul_nonneg (sq_nonneg z.1) hxy.le]
  have h1 : ∫ x in (0 : ℝ)..1, log x * Lir 2 (-x) / (1 + x ^ 2) = ∫ z in S, f z ∂μ := by
    rw [setIntegral_prod f hfi, intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx ↦ ?_
    rw [← integral_mul_log_div_one_add_mul hx.1.le hx.2,
      intervalIntegral.integral_of_le zero_le_one, mul_div_right_comm, ← integral_const_mul]
    congr 1
    ext y
    simp only [hf, div_eq_mul_inv, mul_inv]
    ring
  have h2 : ∫ z in S, f z.swap ∂μ = ∫ z in S, f z ∂μ := setIntegral_prod_swap _ _ f
  have h3 : ∫ z in S, (f z + f z.swap) ∂μ = ∫ z in S, (a z.1 * b z.2 + b z.1 * a z.2) ∂μ := by
    refine setIntegral_congr_fun (measurableSet_Ioc.prod measurableSet_Ioc) fun z hz ↦ ?_
    obtain ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ := hz
    simp only [hf, ha, hb, Prod.fst_swap, Prod.snd_swap]
    have h1x : 0 < 1 + z.1 * z.2 := by positivity
    have h1y : 0 < 1 + z.2 * z.1 := by positivity
    field_simp
    ring
  have h4 : ∫ z in S, (a z.1 * b z.2 + b z.1 * a z.2) ∂μ =
      2 * ((∫ t in Ioc (0 : ℝ) 1, a t) * ∫ t in Ioc (0 : ℝ) 1, b t) := by
    have iab : IntegrableOn (fun z : ℝ × ℝ ↦ a z.1 * b z.2) S μ := by
      rw [IntegrableOn, hμ, hS, ← Measure.prod_restrict]
      exact ia.mul_prod ib
    have iba : IntegrableOn (fun z : ℝ × ℝ ↦ b z.1 * a z.2) S μ := by
      rw [IntegrableOn, hμ, hS, ← Measure.prod_restrict]
      exact ib.mul_prod ia
    rw [integral_add iab iba, hμ, hS, setIntegral_prod_mul, setIntegral_prod_mul]
    ring
  have hA : ∫ t in Ioc (0 : ℝ) 1, a t = -(π ^ 2 / 48) := by
    rw [← intervalIntegral.integral_of_le zero_le_one]
    exact integral_mul_log_div_one_add_sq
  have hB : ∫ t in Ioc (0 : ℝ) 1, b t = -G := by
    rw [← intervalIntegral.integral_of_le zero_le_one]
    exact integral_log_div_one_add_sq
  have hsum := integral_add hfi hfi.swap
  simp only [Function.comp_def] at hsum
  rw [h3, h4, hA, hB, h2] at hsum
  rw [h1]
  linarith

end LeanPolyLog.Arctan
