namespace P2MW.S_LanglandsTunnell_TateLocal_hasDerivAt_localZeta_one_one_integral_mul_log_modulus_of_continuous_of_hasCompactSupport

set_option autoImplicit false

p2m_open

open scoped NNReal ENNReal Pointwise Topology

noncomputable section

namespace LanglandsTunnell

namespace TateLocal

namespace ZetaDeriv

p2m_open

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

section Measure

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
  (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]

theorem integrableOn_norm_rpow_sub_one {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : v.adicCompletion K => ‖x‖ ^ (a - 1))
      {x : v.adicCompletion K | 0 < ‖x‖ ∧ ‖x‖ ≤ 1} μ := by
  obtain ⟨π, hπ0, hπ1⟩ := exists_norm_pos_lt_one v
  have hπne : π ≠ 0 := norm_pos_iff.mp hπ0
  set q : ℝ := ‖π‖ with hq

  set A : ℕ → Set (v.adicCompletion K) := fun n => {x | q ^ (n + 1) < ‖x‖ ∧ ‖x‖ ≤ q ^ n} with hA
  have hcover : {x : v.adicCompletion K | 0 < ‖x‖ ∧ ‖x‖ ≤ 1} ⊆ ⋃ n, A n := by
    intro x hx
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near_of_lt_one hx.1 hx.2 hπ0 hπ1
    exact Set.mem_iUnion.mpr ⟨n, hn1, hn2⟩
  refine IntegrableOn.mono_set ?_ hcover
  have hmeasA : ∀ n, MeasurableSet (A n) := fun n =>
    (measurableSet_lt measurable_const measurable_norm).inter (measurableSet_le measurable_norm measurable_const)
  have hBfin := measure_closedBall_one_lt_top v μ
  have hB : ∀ n : ℕ, μ (A n) ≤ (‖π‖₊ : ℝ≥0∞) ^ n * μ (Metric.closedBall (0 : v.adicCompletion K) 1) := by
    intro n
    rw [← measure_closedBall_pow v μ hπne n]
    exact measure_mono fun x hx => by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hx.2
  have hAfin : ∀ n, μ (A n) < ∞ := fun n =>
    (hB n).trans_lt (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hBfin)
  have hmeas : Measurable fun x : v.adicCompletion K => ‖x‖ ^ (a - 1) := measurable_norm.pow_const _

  have hbound : ∀ n, ∀ x ∈ A n, ‖(‖x‖ ^ (a - 1) : ℝ)‖ ≤ (q ^ n) ^ a * (q ^ (n + 1))⁻¹ := by
    intro n x hx
    have hx0 : 0 < ‖x‖ := lt_trans (pow_pos hπ0 _) hx.1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), Real.rpow_sub_one hx0.ne',
      div_eq_mul_inv]
    exact mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) hx.2 ha.le) (inv_anti₀ (pow_pos hπ0 _) hx.1.le)
      (inv_nonneg.mpr hx0.le) (Real.rpow_nonneg (pow_nonneg hπ0.le _) _)
  have hqpow : ∀ n : ℕ, (q ^ n) ^ a = (q ^ a) ^ n := fun n => by
    rw [← Real.rpow_natCast q n, ← Real.rpow_mul hπ0.le, mul_comm, Real.rpow_mul hπ0.le, Real.rpow_natCast]
  apply integrableOn_iUnion_of_summable_integral_norm
  · intro n
    exact Measure.integrableOn_of_bounded (hAfin n).ne hmeas.aestronglyMeasurable
      ((ae_restrict_mem (hmeasA n)).mono fun x hx => hbound n x hx)
  · have hqa : q ^ a < 1 := Real.rpow_lt_one hπ0.le hπ1 ha
    have hqa0 : 0 ≤ q ^ a := Real.rpow_nonneg hπ0.le _
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_)
      ((summable_geometric_of_lt_one hqa0 hqa).mul_right
        (q⁻¹ * μ.real (Metric.closedBall (0 : v.adicCompletion K) 1)))

    have h1 := norm_setIntegral_le_of_norm_le_const (hAfin n) (fun x hx => by
      rw [norm_norm]; exact hbound n x hx) (f := fun x : v.adicCompletion K => ‖(‖x‖ ^ (a - 1) : ℝ)‖) (μ := μ)
    have h2 : μ.real (A n) ≤ q ^ n * μ.real (Metric.closedBall (0 : v.adicCompletion K) 1) := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hBfin.ne) (hB n)
      rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm] at this
      exact this
    calc ∫ x in A n, ‖(‖x‖ ^ (a - 1) : ℝ)‖ ∂μ
        ≤ ‖∫ x in A n, ‖(‖x‖ ^ (a - 1) : ℝ)‖ ∂μ‖ := Real.le_norm_self _
      _ ≤ (q ^ n) ^ a * (q ^ (n + 1))⁻¹ * μ.real (A n) := h1
      _ ≤ (q ^ n) ^ a * (q ^ (n + 1))⁻¹ * (q ^ n * μ.real (Metric.closedBall (0 : v.adicCompletion K) 1)) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg (Real.rpow_nonneg (pow_nonneg hπ0.le _) _)
            (inv_nonneg.mpr (pow_nonneg hπ0.le _)))
      _ = (q ^ a) ^ n * (q⁻¹ * μ.real (Metric.closedBall (0 : v.adicCompletion K) 1)) := by
          rw [hqpow, pow_succ, mul_inv]
          field_simp

end Measure
end ZetaDeriv
end TateLocal
end LanglandsTunnell
end
end P2MW.S_LanglandsTunnell_TateLocal_hasDerivAt_localZeta_one_one_integral_mul_log_modulus_of_continuous_of_hasCompactSupport
