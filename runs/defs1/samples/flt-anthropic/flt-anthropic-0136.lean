namespace P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization

attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar

open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

open IsDedekindDomain

open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped Classical

open NumberField IsDedekindDomain NumberField.TateGlobal AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

noncomputable section

namespace Ws31

namespace Unfold

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm

open IsDedekindDomain NumberField.TateGlobal Filter Topology

open scoped NNReal ENNReal ComplexConjugate

section Prelim

variable (F : Type) [Field F] [NumberField F]

def wt (p : ((AdeleRing (𝓞 F) F × (AdeleRing (𝓞 F) F)ˣ) × (AdeleRing (𝓞 F) F)ˣ) × adelicMaximalCompact F) : ℝ≥0∞ :=
  ENNReal.ofReal ((ideleNorm F p.1.2)⁻¹)

end Prelim
end Unfold
end Ws31
end
end P2MW.S_AutomorphicForm_exists_forall_norm_iwasawa_integral_axis_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization
