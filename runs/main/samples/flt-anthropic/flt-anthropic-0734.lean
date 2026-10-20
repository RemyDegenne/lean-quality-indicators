namespace P2MW.S_AutomorphicForm_exists_rankinSelberg_testData_of_isArithGenuineCuspRealizable_rat

attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar FLT.SpectralSide.instCompactSpaceMatrix

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain

open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates

open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker

namespace DataRS

open ComplexConjugate

section TorusMatrices

variable {K : Type*} [Field K]

theorem val_scalarPi_zpow (π : K) (hπ : π ≠ 0) (n : ℤ) (i j : Fin 2) :
    ((scalarPi π hπ ^ n : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j = if i = j then π ^ n else 0 := by
  rw [scalarPi_eq_scalar, ← map_zpow]
  show (Matrix.scalar (Fin 2) (((Units.mk0 π hπ) ^ n : Kˣ) : K)) i j = _
  rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, Matrix.scalar_apply, Matrix.diagonal_apply]

end TorusMatrices
end DataRS
end P2MW.S_AutomorphicForm_exists_rankinSelberg_testData_of_isArithGenuineCuspRealizable_rat
