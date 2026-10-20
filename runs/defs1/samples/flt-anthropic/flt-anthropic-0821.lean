namespace P2MW.S_Ideal_isReduced_quotient_tensorProduct_sup_and_natCard_primeSpectrum_eq_card_of_radical_witness

set_option autoImplicit false

open Polynomial TensorProduct

namespace CrossingCount

section poly

variable {K : Type*} [Field K]

noncomputable def quotientSpanProdXSubCEquiv (S : Finset K) :
    (K[X] ⧸ Ideal.span {∏ a ∈ S, (X - C a)}) ≃+* (↥S → K) := by
  classical
  have hcop : Pairwise fun a b : ↥S => IsCoprime (X - C (a : K)) (X - C (b : K)) :=
    fun a b hab => Polynomial.pairwise_coprime_X_sub_C (K := K) (fun x y hxy => hxy)
      (fun h => hab (Subtype.ext h))
  have hinf : Ideal.span {∏ a ∈ S, (X - C a)} = ⨅ a : ↥S, Ideal.span {X - C (a : K)} := by
    rw [Ideal.iInf_span_singleton hcop, ← Finset.prod_coe_sort S]
  refine (Ideal.quotEquivOfEq hinf).trans ?_
  refine (Ideal.quotientInfRingEquivPiQuotient _ fun a b hab => ?_).trans ?_
  · exact (Ideal.isCoprime_span_singleton_iff _ _).mpr (hcop hab)
  · exact RingEquiv.piCongrRight fun a => (Polynomial.quotientSpanXSubCAlgEquiv (a : K)).toRingEquiv

end poly
end CrossingCount
end P2MW.S_Ideal_isReduced_quotient_tensorProduct_sup_and_natCard_primeSpectrum_eq_card_of_radical_witness
