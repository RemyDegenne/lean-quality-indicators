@[expose] public section

open Filter MeasureTheory Set

open scoped ENNReal NNReal Topology

namespace QuadraticCarleson

namespace KaltonEndpoint

theorem integralOn_le_of_weakL1Bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A m M : ℝ} {f : α → ℝ} {s : Set α}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hweak : HasWeakL1Bound μ A f) (hs : MeasurableSet s)
    (hsfinite : μ s ≠ ∞) (hsm : μ.real s ≤ m)
    (hcap : ∀ x ∈ s, f x ≤ M) (hA : 0 < A) (hm : 0 < m)
    (hqM : 2 * A / m ≤ M) :
    ∫ x in s, f x ∂μ ≤ 2 * A + 2 * A * Real.log (M * m / (2 * A)) := by
  let ν : Measure α := μ.restrict s
  let q : ℝ := 2 * A / m
  have hq : 0 < q := by dsimp [q]; positivity
  have hM : 0 < M := lt_of_lt_of_le hq hqM
  let : IsFiniteMeasure ν :=
    IsFiniteMeasure.mk (by
      dsimp [ν]
      rw [Measure.restrict_apply_univ]
      exact lt_top_iff_ne_top.mpr hsfinite)
  have hfint : Integrable f ν := by
    apply Integrable.of_bound hf.aestronglyMeasurable M
    rw [ae_restrict_iff' hs]
    exact Eventually.of_forall fun x hx ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
      exact hcap x hx
  have hlayer := hfint.integral_eq_integral_Ioc_meas_le
    (Eventually.of_forall hf0)
    (show f ≤ᵐ[ν] (fun _ ↦ M) by
      exact ae_restrict_of_forall_mem hs hcap)
  let g : ℝ → ℝ := fun t ↦ ν.real {x | t ≤ f x}
  have hgmeas : StronglyMeasurable g := by
    apply Measurable.stronglyMeasurable
    apply Measurable.ennreal_toReal
    exact Antitone.measurable fun a b hab ↦
      measure_mono fun x hx ↦ le_trans hab hx
  have glow : ∀ t ∈ Ioc (0 : ℝ) q, g t ≤ m := by
    intro t ht
    calc
      g t ≤ ν.real univ := measureReal_mono (subset_univ _) (measure_ne_top ν univ)
      _ = μ.real s := by simp [ν, measureReal_def]
      _ ≤ m := hsm
  have ghigh : ∀ t ∈ Ioc q M, g t ≤ 2 * A / t := by
    intro t ht
    dsimp [g, ν]
    exact hweak.restrict_measureReal_le_two_div s (hq.trans ht.1)
  have hconst_int : IntegrableOn (fun _ : ℝ ↦ m) (Ioc 0 q) volume :=
    integrableOn_const (by simp [Real.volume_Ioc] : volume (Ioc (0 : ℝ) q) ≠ ∞)
  have hg_low : IntegrableOn g (Ioc (0 : ℝ) q) volume := by
    apply Integrable.mono' hconst_int
    · exact hgmeas.aestronglyMeasurable.restrict
    · rw [ae_restrict_iff' measurableSet_Ioc]
      exact Eventually.of_forall fun t ht ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · exact glow t ht
        · exact measureReal_nonneg
  have htail_cont : ContinuousOn (fun t : ℝ ↦ 2 * A / t) (uIcc q M) := by
    apply continuousOn_const.div continuousOn_id
    intro t ht t0
    have htq : q ≤ t := by
      rw [uIcc_of_le hqM] at ht
      exact ht.1
    dsimp only [id_eq] at t0
    linarith
  have htail_int : IntegrableOn (fun t : ℝ ↦ 2 * A / t) (Ioc q M) volume :=
    (htail_cont.intervalIntegrable).1
  have hg_high : IntegrableOn g (Ioc q M) volume := by
    apply Integrable.mono' htail_int
    · exact hgmeas.aestronglyMeasurable.restrict
    · rw [ae_restrict_iff' measurableSet_Ioc]
      exact Eventually.of_forall fun t ht ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · exact ghigh t ht
        · exact measureReal_nonneg
  have hsplit : Ioc (0 : ℝ) M = Ioc 0 q ∪ Ioc q M :=
    (Ioc_union_Ioc_eq_Ioc hq.le hqM).symm
  have hgintegrable : IntegrableOn g (Ioc (0 : ℝ) M) volume := by
    rw [hsplit]
    exact hg_low.union hg_high
  rw [show (∫ x in s, f x ∂μ) = ∫ x, f x ∂ν by rfl, hlayer]
  rw [hsplit, setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
    hg_low hg_high]
  calc
    (∫ t in Ioc 0 q, g t) + ∫ t in Ioc q M, g t ≤
        (∫ _t in Ioc 0 q, m) + ∫ t in Ioc q M, 2 * A / t :=
      add_le_add
        (setIntegral_mono_on hg_low hconst_int measurableSet_Ioc glow)
        (setIntegral_mono_on hg_high htail_int measurableSet_Ioc ghigh)
    _ = m * q + 2 * A * Real.log (M / q) := by
      rw [show (∫ _t in Ioc (0 : ℝ) q, m) = m * q by
        rw [setIntegral_const, measureReal_def, Real.volume_Ioc,
          ENNReal.toReal_ofReal (by linarith)]
        simp [smul_eq_mul, mul_comm]]
      rw [← intervalIntegral.integral_of_le hqM]
      rw [show (fun t : ℝ ↦ 2 * A / t) = fun t ↦ (2 * A) * (1 / t) by
        funext t
        ring]
      rw [intervalIntegral.integral_const_mul]
      rw [integral_one_div_of_pos hq hM]
    _ = 2 * A + 2 * A * Real.log (M * m / (2 * A)) := by
      dsimp [q]
      congr 1
      · field_simp
      · congr 2
        field_simp

end KaltonEndpoint
end QuadraticCarleson
end
