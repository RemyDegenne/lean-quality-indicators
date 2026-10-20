namespace P2MW.S_AutomorphicForm_exists_torusFamily_centralScalar_mul_diagUnits2_coupled_massOne_restrictedProduct

attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

noncomputable section

namespace TorusFamilyK

section Bochner

open scoped ENNReal

variable {B : Type*} [MeasurableSpace B] {A : Type} [MeasurableSpace A]
  {κ : Type} {G : κ → Type} [∀ k, MeasurableSpace (G k)]

scoped instance instMeasurableSpaceOptTy (Sf : Finset κ) :
    ∀ i, MeasurableSpace (OptTy A G Sf i)
  | none => (inferInstance : MeasurableSpace A)
  | some k => (inferInstance : MeasurableSpace (G (k : κ)))

def optMeas (Sf : Finset κ) (νA : Measure A) (νG : ∀ k, Measure (G k)) : ∀ i, Measure (OptTy A G Sf i)
  | none => νA
  | some k => νG k

end Bochner
end TorusFamilyK
end
end P2MW.S_AutomorphicForm_exists_torusFamily_centralScalar_mul_diagUnits2_coupled_massOne_restrictedProduct
