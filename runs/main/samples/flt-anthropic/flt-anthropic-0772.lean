namespace P2MW.S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay

set_option autoImplicit false

set_option autoImplicit false

p2m_reactivate

p2m_reactivate

p2m_reactivate

noncomputable section

open MeasureTheory AutomorphicForm.ComplexIwasawa M4aP3C.CplxSmooth Real VectorFourier Complex

open M4aP3C.CplxIwasawa (botNormSqC botNormSqC_pos centerC radC_pos radC_sq_eq
  norm_det_div_sqrt_le_radC contDiff_radC)

open scoped ContDiff FourierTransform

namespace M4aP3C

namespace CplxDecay

variable {g : Matrix (Fin 2) (Fin 2) ℂ}

theorem contDiff_cpow_neg_radC (hg : g.det ≠ 0) (u : ℂ) :
    ContDiff ℝ ∞ (fun w => ((radC g w : ℂ)) ^ (-u)) := by
  have hm : (0:ℝ) < ‖g.det‖ / Real.sqrt (botNormSqC g) :=
    div_pos (norm_pos_iff.2 hg) (Real.sqrt_pos.2 (botNormSqC_pos hg))
  have hrange : ∀ w : ℂ, radC g w ∈ Set.Ioi (‖g.det‖ / Real.sqrt (botNormSqC g) / 2) := by
    intro w
    exact Set.mem_Ioi.2 (by nlinarith [norm_det_div_sqrt_le_radC' hg w, radC_pos' hg w])
  have hfun : (fun w => ((radC g w : ℂ)) ^ (-u))
      = (fun y : ℝ => ((y : ℂ)) ^ (-u)) ∘ radC g := rfl
  rw [hfun]
  exact (contDiffOn_ofReal_cpow_neg (by linarith) u).comp_contDiff (contDiff_radC' hg) hrange

end CplxDecay
end M4aP3C
end
end P2MW.S_AutomorphicForm_ComplexIwasawa_norm_fourierIntegral_cpow_radC_mul_le_polyDecay
