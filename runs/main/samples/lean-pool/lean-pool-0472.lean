section

@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory

open scoped Topology ContDiff BigOperators

namespace NavierStokes.OutgoingPulseBounds

open OutgoingSchedule

theorem affineCoefficients_exp_bound (c : Parameters) (hsmall : c.lam ≤ 1 / 120)
    (q A : ℝ) (j : Fin 2) :
    |affineCoefficients c q A j| ≤
      coefficientBound c.P c.m * Real.exp (-(1 / (4 * c.lam))) * (|q| + |A|) := by
  have h0 := affineDebt_normalized_bound c hsmall q A 0
  have h1 := affineDebt_normalized_bound c hsmall q A 1
  have hc := actual_coefficients_bound c (affineDebt c q A) j
  change c.lam * |affineCoefficients c q A j| ≤ _ at hc
  have hsum := mul_le_mul_of_nonneg_left (add_le_add h0 h1) inverseBound_pos.le
  have hbase : |affineCoefficients c q A j| ≤
      (inverseBound * (debtBound c.P c.m 0 + debtBound c.P c.m 1)) *
        (Real.exp (-(1 / (2 * c.lam))) / c.lam ^ 2) * (|q| + |A|) := by
    apply (mul_le_mul_iff_right₀ c.lam_pos).mp
    refine hc.trans (hsum.trans_eq ?_)
    field_simp [c.lam_pos.ne']
  have hK : 0 ≤ inverseBound * (debtBound c.P c.m 0 + debtBound c.P c.m 1) :=
    mul_nonneg inverseBound_pos.le (add_nonneg (debtBound_pos c.P_pos c.m 0).le
      (debtBound_pos c.P_pos c.m 1).le)
  calc
    _ ≤ _ := hbase
    _ ≤ (inverseBound * (debtBound c.P c.m 0 + debtBound c.P c.m 1)) *
        (64 * Real.exp (-(1 / (4 * c.lam)))) * (|q| + |A|) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (inverse_square_exp_absorption c.lam_pos) hK)
        (by positivity)
    _ = _ := by unfold coefficientBound; ring

end NavierStokes.OutgoingPulseBounds
end
end
end
