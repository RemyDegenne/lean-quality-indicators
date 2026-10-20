namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe_of_cuspidal

attribute [-instance] IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section ASM_D2Z_Body_DetLB_v1

set_option autoImplicit false

set_option linter.unusedVariables false

p2m_open

open scoped nonZeroDivisors

open NumberField.AdelicLevel (diagOne)

open scoped Classical

namespace D2Z

noncomputable section

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)

local notation "G₂" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem lb_isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel ℚ p
    (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  letI := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  set c : NNReal := (Ideal.absNorm p.asIdeal : NNReal) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot))).ne'
  have hdef : selfDualHaarAt ℚ p = (c : ENNReal) • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

end
end D2Z
end ASM_D2Z_Body_DetLB_v1
end P2MW.S_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe_of_cuspidal
