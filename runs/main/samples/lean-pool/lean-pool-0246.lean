@[expose] public section

universe u v

theorem vcdim_finite_imp_rademacher_vanishing (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (hvcdim : VCDim X C < ⊤) :
    ∀ ε > 0, ∃ m₀, ∀ (D : MeasureTheory.Measure X),
      MeasureTheory.IsProbabilityMeasure D →
      ∀ m ≥ m₀, RademacherComplexity X C D m < ε := by
  rw [WithTop.lt_top_iff_ne_top] at hvcdim
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hvcdim
  intro ε hε
  -- For ε > 1: Rad ≤ 1 < ε.
  by_cases hε1 : 1 < ε
  · use 1; intro D hD m hm
    have : MeasureTheory.IsProbabilityMeasure
        (MeasureTheory.Measure.pi (fun _ : Fin m => D)) :=
      MeasureTheory.Measure.pi.instIsProbabilityMeasure _
    exact lt_of_le_of_lt (rademacherComplexity_le_one X C D m (by omega)) hε1
  · push Not at hε1
    -- ε ≤ 1: use VCDim bound. For d > 0, Rad ≤ √(2d·log(em/d)/m) < ε for large m.
    -- For d = 0: Rad ≤ 1/√m < ε for large m (Khintchine).
    -- The analytical chain: 2d·log(em/d)/m → 0 as m → ∞.
    -- Pick m₀ = max(d+1, ⌈32(d+1)/ε⁴⌉ + 1).
    use max (d + 1) (Nat.ceil (32 * (↑d + 1) / ε ^ 4) + 1)
    intro D hD m hm
    have hm_pos : 0 < m := by omega
    have : MeasureTheory.IsProbabilityMeasure
        (MeasureTheory.Measure.pi (fun _ : Fin m => D)) :=
      MeasureTheory.Measure.pi.instIsProbabilityMeasure _
    by_cases hd_pos : d = 0
    · -- d = 0: use Khintchine bound Rad ≤ 1/√m < ε for large m.
      have hd0 : VCDim X C = (0 : ℕ) := by rw [← hd]; subst hd_pos; rfl
      have h_bound := vcdim_zero_rademacher_le_inv_sqrt X C D hd0 m hm_pos
      calc RademacherComplexity X C D m
          ≤ 1 / Real.sqrt m := h_bound
        _ < ε := by
          rw [div_lt_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm_pos))]
          -- Need: 1 < ε · √m. Suffices: 1/ε² < m.
          -- m ≥ ⌈32/ε⁴⌉+1 > 32/ε⁴ ≥ 1/ε² (since ε ≤ 1).
          have hm_ge : (⌈32 * ((d : ℝ) + 1) / ε ^ 4⌉₊ + 1 : ℕ) ≤ m := by omega
          have h_ceil_le_m : (32 * ((d : ℝ) + 1) / ε ^ 4 : ℝ) < m := by
            calc (32 * ((d : ℝ) + 1) / ε ^ 4 : ℝ)
                ≤ ↑(⌈32 * ((d : ℝ) + 1) / ε ^ 4⌉₊) := Nat.le_ceil _
              _ < (m : ℝ) := by exact_mod_cast (by omega : ⌈32 * ((d : ℝ) + 1) / ε ^ 4⌉₊ < m)
          subst hd_pos; simp only [Nat.cast_zero, zero_add, mul_one] at h_ceil_le_m
          -- 32/ε⁴ < m. Need: 1 < ε·√m.
          -- 1/ε² ≤ 32/ε⁴ < m (since ε ≤ 1 ⟹ 1/ε² ≤ 32/ε⁴).
          -- So m > 1/ε², hence √m > 1/ε, hence ε·√m > 1.
          have hε2_pos : (0 : ℝ) < ε ^ 2 := by positivity
          have h_inv_eps2_lt_m : 1 / ε ^ 2 < (m : ℝ) := by
            have : 1 / ε ^ 2 ≤ 32 / ε ^ 4 := by
              rw [div_le_div_iff₀ hε2_pos (by positivity)]
              -- Need: ε⁴ ≤ 32·ε², i.e., ε² ≤ 32. True since ε ≤ 1.
              have : ε ^ 2 ≤ 1 := by nlinarith
              nlinarith
            linarith
          -- √m > 1/ε, so ε·√m > 1
          have h_sqrt_m : 1 / ε < Real.sqrt m := by
            rw [Real.lt_sqrt (by positivity)]
            simp_all
          -- ε * (1/ε) = 1, and ε * √m > ε * (1/ε) = 1
          have : ε * (1 / ε) = 1 := by field_simp
          nlinarith [mul_lt_mul_of_pos_left h_sqrt_m hε]
    · -- d > 0: Rad ≤ √(2d·log(em/d)/m) < ε.
      have hd_pos' : 0 < d := Nat.pos_of_ne_zero hd_pos
      have hdm : d ≤ m := by omega
      have h_quant := vcdim_bounds_rademacher_quantitative X C D m hm_pos d hd.symm hd_pos' hdm
      have h_anal := analytical_log_sqrt_bound d m ε hε hε1 hd_pos' hdm (by omega)
      calc RademacherComplexity X C D m
          ≤ Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑m / ↑d) / ↑m) := h_quant
        _ < Real.sqrt (ε ^ 2) := by
            apply Real.sqrt_lt_sqrt
            · apply div_nonneg
              · apply mul_nonneg
                · simp_all
                · exact Real.log_nonneg (by
                    rw [le_div_iff₀ (Nat.cast_pos.mpr hd_pos')]
                    have hd_r : (0 : ℝ) < d := Nat.cast_pos.mpr hd_pos'
                    have hm_r : (d : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hdm
                    have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
                    nlinarith [Real.add_one_le_exp (1 : ℝ)])
              · exact Nat.cast_nonneg m
            · exact h_anal
        _ = ε := by rw [Real.sqrt_sq (le_of_lt hε)]

end
