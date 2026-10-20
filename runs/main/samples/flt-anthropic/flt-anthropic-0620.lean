namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_integral_hermiteBracket_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightZeroLevi

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open NumberField AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell LanglandsTunnell.CubicInduction MeasureTheory

namespace Ws23PhiFlatM

open LanglandsTunnell.Converse.ArchR Set

theorem deriv_Gc (η : ℝ) :
    deriv (fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ)) η = -(2 * Real.pi * η) * (Real.exp (-(Real.pi * η ^ 2)) : ℂ) := by
  have h1 : HasDerivAt (fun y : ℝ => -(Real.pi * y ^ 2)) (-(Real.pi * (2 * η))) η := by
    first
      | simpa [pow_one] using ((hasDerivAt_pow 2 η).const_mul Real.pi).neg
      | (simpa [pow_one] using (((hasDerivAt_pow 2 η).const_mul Real.pi).neg :)) | (simpa [Function.comp_def] using ((hasDerivAt_pow 2 η).const_mul Real.pi).neg) | exact ((hasDerivAt_pow 2 η).const_mul Real.pi).neg | (have h__ := ((hasDerivAt_pow 2 η).const_mul Real.pi).neg; (try simp [pow_one] at h__); (try simp [pow_one]); exact h__)
  have h3 : HasDerivAt (fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ))
      (((Real.exp (-(Real.pi * η ^ 2)) * -(Real.pi * (2 * η)) : ℝ) : ℂ)) η :=
    ((Real.hasDerivAt_exp _).comp η h1).ofReal_comp
  rw [h3.deriv]
  push_cast
  ring

end Ws23PhiFlatM
end P2MW.S_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_integral_hermiteBracket_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightZeroLevi
