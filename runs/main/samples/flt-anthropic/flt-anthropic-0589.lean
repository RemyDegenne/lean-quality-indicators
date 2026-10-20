namespace P2MW.S_AutomorphicForm_exists_forall_norm_ratio_mul_sqrtRatio_mul_twistedWeighted_add_mul_log_mul_twistedOrbital_sub_le_of_normString_diagUnits2_eq

attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct TensorProduct.RightActions Pointwise

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option synthInstance.maxHeartbeats 320000

open NumberField IsDedekindDomain MeasureTheory Set Function

open scoped ENNReal NNReal TensorProduct TensorProduct.RightActions Pointwise

namespace TwLogExp

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable {v : HeightOneSpectrum (𝓞 K)}

open scoped TensorProduct TensorProduct.RightActions

attribute [local instance 9999] Algebra.toModule

local notation "F" => v.adicCompletion K

local notation "E" => L ⊗[K] v.adicCompletion K

local notation "G" => GL (Fin 2) (L ⊗[K] v.adicCompletion K)

local notation "𝒦" => AutomorphicForm.semiLocalIntegralSet K L v

section SliceShift28

theorem ss28_diagUnits2_one_inv (u : Fˣ) : (diagUnits2 (1 : Fˣ) u)⁻¹ = diagUnits2 1 u⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, LanglandsTunnell.CubicInduction.coe_diagUnits2]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end SliceShift28
end TwLogExp
end P2MW.S_AutomorphicForm_exists_forall_norm_ratio_mul_sqrtRatio_mul_twistedWeighted_add_mul_log_mul_twistedOrbital_sub_le_of_normString_diagUnits2_eq
