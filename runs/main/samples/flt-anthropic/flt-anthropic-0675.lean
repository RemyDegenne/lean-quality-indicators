namespace P2MW.S_CerednikDrinfeld_CSTower_exists_finiteIdeleDiagonal_mul_inv_mem_levelHeckeUSet_meetOrder_isEichlerOrder_of_dvd

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

namespace MUCST

section Global

variable {a b : ℚ} (p : ℕ) (hp : p.Prime)

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ (place p hp)

local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ (place p hp)

local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place p hp))

local notation "ℍv" => ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ (place p hp)

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

variable (φ : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ (place p hp) ≃+*
    Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place p hp)))
  (hφ : ∀ r : HeightOneSpectrum.adicCompletion ℚ (place p hp),
    φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place p hp))))
  (g : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place p hp)))
  (Λ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ) (hΛ₂ : QuaternionAlgebra.IsOrder Λ₂)
  (hgΛ : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ (place p hp),
    x ∈ Submodule.localBox Λ (place p hp) ↔ coord p hp φ g x ∈ intMat p hp)
  (hgΛ₂ : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ (place p hp),
    x ∈ Submodule.localBox Λ₂ (place p hp) ↔ diM p hp * coord p hp φ g x * dM p hp ∈ intMat p hp)
  (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : R = Λ ⊓ Λ₂)

omit hp in
theorem evalAt_inv_val (w : HeightOneSpectrum (𝓞 ℚ)) (m : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) =
      (((unitAt w m)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :=
  (coe_inv_unitAt w m).symm

end Global
end MUCST
end
end P2MW.S_CerednikDrinfeld_CSTower_exists_finiteIdeleDiagonal_mul_inv_mem_levelHeckeUSet_meetOrder_isEichlerOrder_of_dvd
