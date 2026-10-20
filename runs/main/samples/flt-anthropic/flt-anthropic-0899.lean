namespace P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq

attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option synthInstance.maxHeartbeats 320000

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace TensorProduct

open scoped TensorProduct.RightActions

attribute [-instance] LanglandsTunnell.CubicInduction.countable_GL2
  LanglandsTunnell.CubicInduction.countable_mirabolicIndex

noncomputable section

p2m_reactivate

p2m_reactivate

section P3

open NumberField IsDedekindDomain MeasureTheory Set Function

open scoped ENNReal NNReal TensorProduct TensorProduct.RightActions Pointwise

namespace KcSemiLocalIwasawaHaar

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => v.adicCompletion K

local notation "E" => L ⊗[K] v.adicCompletion K

local notation "Q" => (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K)

local notation "G" => GL (Fin 2) (L ⊗[K] v.adicCompletion K)

attribute [local instance 9999] Algebra.toModule

attribute [local instance] isTopologicalRing_E t2Space_E locallyCompactSpace_E continuousSMul_E
  isScalarTower_FEE smulCommClass_FEE finite_KL

attribute [local instance] secondCountableTopology_E

p2m_reactivate

attribute [local instance] t2Space_GL secondCountableTopology_GL locallyCompactSpace_GL
  isTopologicalGroup_GL measurableSpace_GL

attribute [local instance] borelSpace_GL isHaarMeasure_semiLocalHaar

attribute [local instance] measurableMul_GL measurableInv_GL

local notation "μG" => AutomorphicForm.semiLocalHaar K L v

local notation "𝒦" => AutomorphicForm.semiLocalIntegralSet K L v

local notation "𝒪" => AutomorphicForm.semiLocalIntegers K L v

p2m_reactivate

section Kgroup

theorem K_mul_mem {g h : G} (hg : g ∈ 𝒦) (hh : h ∈ 𝒦) : g * h ∈ 𝒦 := by
  rw [mem_K_iff] at hg hh ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul]; exact matrix_mul_mem hg.1 hh.1 i j
  · rw [mul_inv_rev, Units.val_mul]; exact matrix_mul_mem hh.2 hg.2 i j

end Kgroup
end KcSemiLocalIwasawaHaar
end P3
end
end P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq
