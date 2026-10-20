namespace P2MW.S_AutomorphicForm_CuspidalConstituent_inf_eq_bot_or_le_of_isCuspConstituent_principal

attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain

open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum

open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace F55MinimalityPrincipal

variable (F : Type) [Field F] [NumberField F]

variable (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))

theorem levelAvg_smul (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    levelAvg F U hU (c • φ) = c • levelAvg F U hU φ := by
  funext x
  simp only [levelAvg, Pi.smul_apply, smul_eq_mul]
  exact integral_const_mul c _

end F55MinimalityPrincipal
end
end P2MW.S_AutomorphicForm_CuspidalConstituent_inf_eq_bot_or_le_of_isCuspConstituent_principal
