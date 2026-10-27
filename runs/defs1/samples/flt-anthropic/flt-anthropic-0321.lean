namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_isMaximalOrder_and_eq_inf_and_relIndex_eq_of_squarefree_of_le

attribute [-instance] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option linter.style.multiGoal false

set_option linter.unusedSimpArgs false

set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct Quaternion Pointwise

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace EndVertex

section LocalPackage

variable {a b : ℚ} (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v

local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v

local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)

local notation "ℍv" => ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v

variable (φ : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v ≃+*
    Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
  (h : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

variable (Λ Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]) (e : ℕ) (g : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

variable {v φ h Λ Λ₁ Λ₂ e g} (H : LocalData v φ h Λ Λ₁ Λ₂ e g)

include H

def swapInv (v : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v ≃+*
      Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
    (h : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) (e : ℕ) :
    ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v :=
  φ.symm ((h : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) * ninv v (piPow v e) *
    ((h⁻¹ : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) :
      Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)))

end LocalPackage
end EndVertex
end
end P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_isMaximalOrder_and_eq_inf_and_relIndex_eq_of_squarefree_of_le
