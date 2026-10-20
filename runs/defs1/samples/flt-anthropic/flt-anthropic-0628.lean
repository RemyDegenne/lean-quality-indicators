namespace P2MW.S_CerednikDrinfeld_QM_trace_eq_intCast_of_isTangentVector_prod_of_smoothOfRelativeDimension_one_of_charZero

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

def V₁ (hτ : IsTD (L.prod L) k sk V τ) (W : View L) : Submodule k V where
  carrier := {v | W.po (τ v) = L.one (tangentBase k sk)}
  zero_mem' := by
    show W.po (τ 0) = _
    rw [hτ.zero, W.po_one]
  add_mem' {v w} hv hw := by
    show W.po (τ (v + w)) = _
    rw [hτ.add, W.po_mul, show W.po (τ v) = _ from hv, show W.po (τ w) = _ from hw, L.one_mul]
  smul_mem' c v hv := by
    show W.po (τ (c • v)) = _
    rw [hτ.smul_eq, W.po_natural, show W.po (τ v) = _ from hv]
    exact resPt_one L _ _

end Prod
end P2mX3Beta
end
end P2MW.S_CerednikDrinfeld_QM_trace_eq_intCast_of_isTangentVector_prod_of_smoothOfRelativeDimension_one_of_charZero
