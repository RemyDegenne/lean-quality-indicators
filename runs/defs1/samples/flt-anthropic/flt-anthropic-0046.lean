set_option maxHeartbeats 200000

set_option autoImplicit false

noncomputable section

namespace MvPolynomial.CrossingQuotient

open Polynomial

universe u

variable {W : Type u} [CommRing W] (t : W) (𝔭 : Ideal W) (ht : t ∈ 𝔭)

section lineU

def quotIUEquiv : (CrossingQuotient W t ⧸ IU t 𝔭) ≃ₐ[W] (W ⧸ 𝔭)[X] :=
  AlgEquiv.ofAlgHom (quotIUEquiv_fwd t 𝔭 ht) (quotIUEquiv_bwd t 𝔭) (quotIUEquiv_fwd_bwd t 𝔭 ht)
    (quotIUEquiv_bwd_fwd t 𝔭 ht)

end lineU
end MvPolynomial.CrossingQuotient
end
