set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.TateLocal

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

open IsDedekindDomain.HeightOneSpectrum

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem localLFactorAt_of_not_hasConductorExponentAt_zero {χ : (v.adicCompletion K)ˣ →* ℂˣ}
    (hχ : ¬ HasConductorExponentAt K v χ 0) (s : ℂ) : localLFactorAt K v χ s = 1 := by
  rw [localLFactorAt, if_neg hχ]

end LanglandsTunnell.TateLocal
end
