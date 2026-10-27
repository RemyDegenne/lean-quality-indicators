namespace P2MW.S_AutomorphicForm_exists_isCompact_forall_exists_mem_sigmaCentralizer_eq_mul_of_ideleNorm_det_eq_one_of_forall_ne_scalar_of_finrank_eq_two

attribute [-instance] RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

set_option linter.unusedSectionVars false

open MeasureTheory NumberField Matrix

open scoped TensorProduct TensorProduct.RightActions NNReal ENNReal Pointwise

noncomputable section

namespace P2mFujisakiD

open AutomorphicForm

section Adelic

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

local notation "AK" => AdeleRing (𝓞 K) K

local notation "AL" => AdeleRing (𝓞 L) L

scoped instance secondCountableTopology_adeleRing (F : Type) [Field F] [NumberField F] :
    SecondCountableTopology (AdeleRing (𝓞 F) F) :=
  NumberField.AdeleRing.secondCountableTopology F

variable (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)

abbrev RK : Type := ↥(twistedCommutant K L AK σ (δA K L δ₀ c))

end Adelic
end P2mFujisakiD
end
end P2MW.S_AutomorphicForm_exists_isCompact_forall_exists_mem_sigmaCentralizer_eq_mul_of_ideleNorm_det_eq_one_of_forall_ne_scalar_of_finrank_eq_two
