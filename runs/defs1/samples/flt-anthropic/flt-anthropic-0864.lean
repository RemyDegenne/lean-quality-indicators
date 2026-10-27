namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_span_twist_det_kirillov_eq_indicator_shell_of_localLevelOne

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

noncomputable section

section KBblock

open IsDedekindDomain NumberField

open scoped WithZero Pointwise

namespace KBE4a

section GLtwo

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => HeightOneSpectrum.adicCompletion K v

local notation "Mat" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)

local notation "G" => GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)

def gl2 (a b c d : F) (h : a * d - b * c ≠ 0) : G :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; c, d] (by rwa [Matrix.det_fin_two_of])

end GLtwo
end KBE4a
end KBblock
end
end P2MW.S_LanglandsTunnell_RankinSelberg_exists_mem_span_twist_det_kirillov_eq_indicator_shell_of_localLevelOne
