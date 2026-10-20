namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe_of_borelEigenfunctional

attribute [-instance] IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion

p2m_reactivate

p2m_reactivate

p2m_reactivate

section ASM_Blocks_KW47_KW0ps

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

p2m_reactivate

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal Topology

open scoped NNReal ENNReal

p2m_reactivate

p2m_reactivate

namespace KW47

p2m_open

open scoped NNReal ENNReal

p2m_reactivate

section Main

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)

local notation "G2" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem ofReal_zpow_cpow (q : ℝ) (hq : 0 < q) (j : ℤ) (z : ℂ) :
    (((q ^ j : ℝ)) : ℂ) ^ z = (q : ℂ) ^ ((j : ℂ) * z) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqj : 0 < q ^ j := zpow_pos hq _
  have hqj0 : (((q ^ j : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hqj.ne'
  have hlog1 : Complex.log (((q ^ j : ℝ)) : ℂ) = ((((j : ℤ) : ℝ) * Real.log q : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log hqj.le, Real.log_zpow]
  have hlogq : Complex.log (q : ℂ) = ((Real.log q : ℝ) : ℂ) := (Complex.ofReal_log hq.le).symm
  rw [Complex.cpow_def_of_ne_zero hqj0, hlog1, Complex.cpow_def_of_ne_zero hq0, hlogq]
  congr 1
  push_cast
  ring

end Main
end KW47
end ASM_Blocks_KW47_KW0ps
end P2MW.S_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe_of_borelEigenfunctional
