namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_finiteIdele_meetOrder_isEichlerOrder_mul_of_not_dvd_of_isIndefiniteRamifiedExactlyAt

attribute [-instance] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise

open IsDedekindDomain NumberField

set_option autoImplicit false

open scoped TensorProduct

open IsDedekindDomain NumberField

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise

open IsDedekindDomain NumberField

namespace C8N

open Classical in
noncomputable scoped instance : DecidableEq (HeightOneSpectrum (𝓞 ℚ)) := Classical.decEq _

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

local notation "D_" v => ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v

local notation "ev" v => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v

noncomputable def placeOfPrime (q : ℕ) (hq : q.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  ⟨Ideal.span {(q : 𝓞 ℚ)}, (Nat.isMaximal_span_natCast_of_prime hq).isPrime, Nat.span_natCast_ne_bot hq.ne_zero⟩

end C8N
end P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_finiteIdele_meetOrder_isEichlerOrder_mul_of_not_dvd_of_isIndefiniteRamifiedExactlyAt
