public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal Nat

namespace TauCeti

namespace Probability

variable {μ b x : ℝ}

theorem integrable_laplacePDFReal (μ : ℝ) : Integrable (laplacePDFReal μ b) := by
  by_cases hb : 0 < b
  · rw [← integrableOn_univ, ← Iic_union_Ioi (a := μ)]
    have hIic : IntegrableOn (laplacePDFReal μ b) (Iic μ) := by
      have h : IntegrableOn
          (fun y : ℝ => (2 * b)⁻¹ * Real.exp (-(μ / b)) * Real.exp (b⁻¹ * y)) (Iic μ) :=
        (integrableOn_exp_mul_Iic (inv_pos.mpr hb) μ).const_mul _
      exact h.congr_fun (fun y hy => (laplacePDFReal_eq_left hb hy).symm) measurableSet_Iic
    have hIoi : IntegrableOn (laplacePDFReal μ b) (Ioi μ) := by
      have h : IntegrableOn
          (fun y : ℝ => (2 * b)⁻¹ * Real.exp (μ / b) * Real.exp (-b⁻¹ * y)) (Ioi μ) :=
        (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (inv_pos.mpr hb)) μ).const_mul _
      exact h.congr_fun (fun y (hy : μ < y) => (laplacePDFReal_eq_right hb hy.le).symm)
        measurableSet_Ioi
    exact hIic.union hIoi
  · have hzero : laplacePDFReal μ b = 0 :=
      funext fun y => laplacePDFReal_of_nonpos (not_lt.mp hb) μ y
    rw [hzero]
    exact integrable_zero ℝ ℝ volume

end Probability
end TauCeti
end
end
