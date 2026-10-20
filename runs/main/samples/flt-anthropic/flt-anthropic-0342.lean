namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_casimir1_eq_smul_of_isArchSmooth3

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

open LanglandsTunnell.CubicInduction

noncomputable section

namespace CF1Body48

theorem deriv_exp_curve {F : (Fin 3 → Fin 3 → ℝ) → ℂ} (hF : DifferentiableAt ℝ F I₃) :
    deriv (fun s : ℝ => F (Real.exp s • I₃)) 0 = fderiv ℝ F I₃ I₃ := by
  have hγ : HasDerivAt (fun s : ℝ => Real.exp s • I₃) I₃ 0 := by
    simpa using (Real.hasDerivAt_exp 0).smul_const I₃
  have hx : Real.exp 0 • I₃ = I₃ := by simp
  have hF' : HasFDerivAt F (fderiv ℝ F I₃) (Real.exp 0 • I₃) := by rw [hx]; exact hF.hasFDerivAt
  exact (hF'.comp_hasDerivAt (0 : ℝ) hγ).deriv

end CF1Body48
end
end P2MW.S_LanglandsTunnell_CubicInduction_exists_casimir1_eq_smul_of_isArchSmooth3
