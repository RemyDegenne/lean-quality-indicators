public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green

theorem oneForm_eq_clm (P Q : ℂ → ℝ) :
    oneForm P Q = fun z ↦ P z • Complex.reCLM + Q z • Complex.imCLM := by
  ext z v
  simp [oneForm_apply]

end TauCeti.Green
end
end
