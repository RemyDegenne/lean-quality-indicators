namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_threshold_firstRatioCoeff_flat_regularSingular_system_of_leading_of_casimir_relations

attribute [-instance] RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

open LanglandsTunnell LanglandsTunnell.CubicInduction

open scoped Topology

open Filter

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

open LanglandsTunnell LanglandsTunnell.CubicInduction

open scoped Topology

open Filter

namespace Fold0Aux

abbrev IsOrthArch (k : G3) : Prop :=
  (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) ∧ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3

end Fold0Aux
end P2MW.S_LanglandsTunnell_CubicInduction_exists_threshold_firstRatioCoeff_flat_regularSingular_system_of_leading_of_casimir_relations
