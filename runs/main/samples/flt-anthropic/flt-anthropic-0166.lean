namespace P2MW.S_LanglandsTunnell_Converse_ArchDatumR_W_mul_diag_eq_neg_one_pow_mul_of_principal_of_archWeightChar_zero_of_isCasimirEigen

set_option autoImplicit false

open Real Complex MeasureTheory Set Filter

open NumberField AutomorphicForm

open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse

noncomputable section

namespace DZChi

theorem archWeightCharℝ_zero (r : rowIsometrySubgroup₀ ℝ) : ((archWeightCharℝ 0 r : ℂˣ) : ℂ) = 1 := by
  show (((archWeightOneℝ r) ^ (0 : ℤ) : ℂˣ) : ℂ) = 1
  rw [zpow_zero, Units.val_one]

end DZChi
end
end P2MW.S_LanglandsTunnell_Converse_ArchDatumR_W_mul_diag_eq_neg_one_pow_mul_of_principal_of_archWeightChar_zero_of_isCasimirEigen
