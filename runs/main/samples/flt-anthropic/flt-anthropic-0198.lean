namespace P2MW.S_CerednikDrinfeld_QM_trace_eq_intCast_of_isTangentVector_prod_of_smoothOfRelativeDimension_one

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM

open scoped Quaternion

namespace P2mX3Beta

section Prod

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

variable (k : Type) [Field k] (sk : S →+* k)

variable {L k sk}

variable {V : Type} [AddCommGroup V] [Module k V] {τ : V → SchemeHomOver (tangentBase k sk) (prodStr f f)}

theorem finrank_V₁ [SmoothOfRelativeDimension 1 f] (hτ : IsTD (L.prod L) k sk V τ) (W : View L) :
    Module.finrank k ↥(V₁ hτ W) = 1 :=
  CerednikDrinfeld.QM.finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension L 1 k sk
    (↥(V₁ hτ W)) (τ₁ hτ W) (isTD_τ₁ hτ W).inj (isTD_τ₁ hτ W).range (isTD_τ₁ hτ W).add (isTD_τ₁ hτ W).smul

end Prod
end P2mX3Beta
end
end P2MW.S_CerednikDrinfeld_QM_trace_eq_intCast_of_isTangentVector_prod_of_smoothOfRelativeDimension_one
