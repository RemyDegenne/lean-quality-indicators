namespace P2MW.S_AutomorphicForm_TwistedBruhat_integral_iwasawa_tsum_normOneFibre_eq_integral_unitFibre_of_fibrewise

attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option linter.deprecated false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar

open IsDedekindDomain AutomorphicForm

open scoped Pointwise ENNReal NNReal Topology

noncomputable section

namespace R1IwTorus

section Unfold

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

variable (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

variable {A : AdelicGL2 (𝓞 L) L → ℝ≥0∞} {U : AdelicGL2 (𝓞 L) L → ℂ}

def st (a : N1 K L) (t : (AdeleRing (𝓞 L) L)ˣ) : (AdeleRing (𝓞 L) L)ˣ := (Eid K L σ hgen a)⁻¹ * t

end Unfold
end R1IwTorus
end
end P2MW.S_AutomorphicForm_TwistedBruhat_integral_iwasawa_tsum_normOneFibre_eq_integral_unitFibre_of_fibrewise
