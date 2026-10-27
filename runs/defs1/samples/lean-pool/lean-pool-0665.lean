section

section

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev

open Set Real EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerVolterraConvolution EulerContinuousTimeIntegral

/-- Logarithmic gronwall constant, given by `C*(1+‖A.toLp‖+logEnergyBase
A+gradientEnergyConstant)`. -/
def logarithmicGronwallConstant (C : ℝ) (A : SmoothL2Field Space) : ℝ :=
  C*(1+‖A.toLp‖+logEnergyBase A+gradientEnergyConstant)

end EulerOrdinarySobolev
end
end
end
end
