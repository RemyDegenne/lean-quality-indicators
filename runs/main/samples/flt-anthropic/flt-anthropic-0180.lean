namespace P2MW.S_LanglandsTunnell_CubicInduction_isArchSmooth3_and_sum_smul_iterate_casimir_eq_zero_of_mem_span_foldr_archDeriv_mul_right

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm

namespace R4CentreSpan

open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.WhittakerBlock

open LanglandsTunnell.CubicInduction.SlabL2 (translateRight)

local notation "GA" => AdelicGL 3 (𝓞 ℚ) ℚ

theorem coe_K1 (x : smoothFunctions3) : ((K1 x : smoothFunctions3) : GA → ℂ) = casimir1 (x : GA → ℂ) := by
  funext g
  simp only [K1, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, coe_archDerivₗ_apply, casimir1]

end R4CentreSpan
end
end P2MW.S_LanglandsTunnell_CubicInduction_isArchSmooth3_and_sum_smul_iterate_casimir_eq_zero_of_mem_span_foldr_archDeriv_mul_right
