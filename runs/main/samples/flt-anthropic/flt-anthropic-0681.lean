namespace P2MW.S_NumberField_AdelicFourier_fourierTransform2_mem_schwartzBruhat2_and_reflectPair_mem_schwartzBruhat2

attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions

set_option autoImplicit false

set_option synthInstance.maxSize 1024

p2m_open

open scoped SchwartzMap NNReal ENNReal FourierTransform

noncomputable section

namespace NumberField

namespace AdelicFourier

namespace FT2StableSol

p2m_open

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

section BoxTensor

variable [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
  (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
  [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
  (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure] [SigmaFinite ν]
  {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}

omit [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
  [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] in
theorem continuous_psiF (hψ : Continuous ψ) : Continuous (psiF ψ) := by
  have : (psiF ψ : FiniteAdeleRing (𝓞 F) F → ℂ) = fun y => ψ (((0 : InfiniteAdeleRing F), y) :
      InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) := rfl
  rw [this]
  exact hψ.comp (continuous_const.prodMk continuous_id)

end BoxTensor
end FT2StableSol
end AdelicFourier
end NumberField
end
end P2MW.S_NumberField_AdelicFourier_fourierTransform2_mem_schwartzBruhat2_and_reflectPair_mem_schwartzBruhat2
