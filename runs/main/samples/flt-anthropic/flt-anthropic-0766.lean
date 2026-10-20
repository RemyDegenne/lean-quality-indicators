namespace P2MW.S_LanglandsTunnell_RankinSelberg_matFourier22_kirillov_det_mul_coefficient_eq_of_cuspidal

attribute [-instance] IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

open NumberField.AdelicLevel (diagOne)

open scoped Classical

noncomputable section

namespace WBFKSlotA

section KBblock

open IsDedekindDomain NumberField

open scoped WithZero Pointwise

section GLtwo

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => HeightOneSpectrum.adicCompletion K v

local notation "Mat" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)

local notation "G" => GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)

theorem congr_antitone (n : ℕ) : congr K v (n + 1) ≤ congr K v n := by
  intro g hg
  exact ⟨hg.h00.trans (lvl_succ_le n), hg.h01.trans (lvl_succ_le n), hg.h10.trans (lvl_succ_le n),
    hg.h11.trans (lvl_succ_le n)⟩

end GLtwo
end KBblock
end WBFKSlotA
end
end P2MW.S_LanglandsTunnell_RankinSelberg_matFourier22_kirillov_det_mul_coefficient_eq_of_cuspidal
