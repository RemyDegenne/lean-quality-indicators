namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_le_setIntegral_localLevelOne_mul_diagZ_mul_eq_zero_of_sqrt_modulus_tail_of_forall_torusZeta_polynomial

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal UnramifiedWhittaker Topology Filter

open scoped NNReal ENNReal Classical Pointwise

p2m_reactivate

namespace TorusMultOne

open Rat.HeightOneSpectrum

section Span

variable {G : Type*} [Group G]

theorem self_translate_mem_cyc (W₀ : G → ℂ) (h : G) : (fun g => W₀ (g * h)) ∈ cyc W₀ :=
  Submodule.subset_span ⟨h, rfl⟩

end Span
end TorusMultOne
end
end P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_le_setIntegral_localLevelOne_mul_diagZ_mul_eq_zero_of_sqrt_modulus_tail_of_forall_torusZeta_polynomial
