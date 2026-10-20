namespace P2MW.S_LanglandsTunnell_RankinSelberg_measure_pi_selfDualHaarAt_setOf_apply_eq_zero_or_det_eq_zero

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

open scoped ENNReal

noncomputable section

namespace GJHLA

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ

theorem isAddHaarMeasure_selfDualHaarAt :
    letI : MeasurableSpace F := localBorel ℚ p
    (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  letI : MeasurableSpace F := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  unfold selfDualHaarAt
  refine Measure.IsAddHaarMeasure.nnreal_smul _ ?_
  have hq : (0 : NNReal) < (Ideal.absNorm p.asIdeal : NNReal) :=
    zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p)
  exact (NNReal.rpow_pos hq).ne'

end GJHLA
end
end P2MW.S_LanglandsTunnell_RankinSelberg_measure_pi_selfDualHaarAt_setOf_apply_eq_zero_or_det_eq_zero
