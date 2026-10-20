namespace P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 6400000

scoped instance instCharZeroAdicCompletionRingOfIntegers_s18 {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    CharZero (v.adicCompletion K) :=
  ((algebraMap K (v.adicCompletion K)).charZero_iff (algebraMap K (v.adicCompletion K)).injective).mp inferInstance

scoped instance fact_prime_two_s18 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

scoped instance fact_prime_three_s18 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

scoped instance fact_prime_seven_s18 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

section

set_option maxHeartbeats 1600000

set_option maxRecDepth 8000

noncomputable section

namespace FLT

namespace JpssD4KubotaFiniteAdelicProductObjectSlice

open FLT.CampGenuineMk

open FLT.JpssD4GJProp83MetaplecticKubotaCoverCarrier

open FLT.JpssD4KubotaPTwoHilbertTable

open FLT.JpssD4KubotaArchimedeanCocycleSlice

open FLT.JpssD4KubotaGlobalProductFormulaSlice

open FLT.JpssD4KubotaTameSymbolUniformWindowSlice

def jpd4r17t5_oddComplementProduct (a b : ℤ) : ℤˣ :=
  ∏ p ∈ jpd4r17t5_oddSupport (a * b), jpd4r17t5_oddLocalFactor p a b

end JpssD4KubotaFiniteAdelicProductObjectSlice
end FLT
end
end
end
end P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero
