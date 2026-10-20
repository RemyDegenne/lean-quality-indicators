namespace P2MW.S_UnramifiedWhittaker_eq_of_forall_unipotent_of_localLevelOne_of_scalarPi_of_diagZ

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker

noncomputable section

namespace SlSph

open WithZero

variable (v : HeightOneSpectrum (𝓞 ℚ))

def wK : GL (Fin 2) (Fv v) :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

end SlSph
end
end P2MW.S_UnramifiedWhittaker_eq_of_forall_unipotent_of_localLevelOne_of_scalarPi_of_diagZ
