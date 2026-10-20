namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3_of_weightZero_profile

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSimpArgs false

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse

open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory

namespace Ws14P0pt

theorem quasiChar_neg (u : ℂ) (a : ZMod 2) (y : ℝ) :
    ArchR.quasiChar u a (-y) = (-1 : ℂ) ^ a.val * ArchR.quasiChar u a y := by
  unfold ArchR.quasiChar
  rw [abs_neg, Left.sign_neg]
  rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) a with rfl | rfl
  · simp
  · simp only [show (1 : ZMod 2) ≠ 0 from by decide, if_false, show (1 : ZMod 2).val = 1 from rfl, pow_one]
    push_cast; ring

end Ws14P0pt
end
end P2MW.S_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3_of_weightZero_profile
