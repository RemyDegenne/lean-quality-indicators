namespace P2MW.S_LanglandsTunnell_CubicInduction_casimir_apply_eq_sum_deriv_archRealLift3_mul

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

p2m_open

open LanglandsTunnell.CubicInduction.WhittakerBlock

noncomputable section

namespace LanglandsTunnell

namespace CubicInduction

namespace RwCasAsm

p2m_open

theorem ind_eq_single (i j : Fin 3) : ind i j = Matrix.single i j (1 : ℝ) := by
  funext a b
  simp only [ind, Matrix.single_apply]
  by_cases h1 : a = i <;> by_cases h2 : b = j
  · subst h1; subst h2; simp
  · subst h1; rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 h.2.symm)]
  · subst h2; rw [if_neg (fun h => h1 h.1), if_neg (fun h => h1 h.1.symm)]
  · rw [if_neg (fun h => h1 h.1), if_neg (fun h => h1 h.1.symm)]

end RwCasAsm
end CubicInduction
end LanglandsTunnell
end
end P2MW.S_LanglandsTunnell_CubicInduction_casimir_apply_eq_sum_deriv_archRealLift3_mul
