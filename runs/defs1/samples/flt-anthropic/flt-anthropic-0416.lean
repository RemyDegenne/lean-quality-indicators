namespace P2MW.S_LanglandsTunnell_CubicInduction_isCubicInductionDataOn_twist_det

attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse

p2m_open

noncomputable section

namespace TwistDataOn

variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
  (pins : AutomorphicForm.CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
  (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (F : CubicInductionForm K pins ψ ν) (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)

def chiDet (x : AdelicGL 3 (𝓞 ℚ) ℚ) : ℂ := ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ)

end TwistDataOn
end
end P2MW.S_LanglandsTunnell_CubicInduction_isCubicInductionDataOn_twist_det
