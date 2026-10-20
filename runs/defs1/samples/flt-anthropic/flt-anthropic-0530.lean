namespace P2MW.S_M4aHerbrand_infiniteIdeleFibre_tateCard_eq_localDegreeProd

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace P2mS26UnivA

noncomputable section

open IsDedekindDomain NumberField

universe uK uL

attribute [local instance] small

section models

variable (K : Type uK) (L : Type uL) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] numberField

attribute [local instance] alg

def gal (σ : L ≃ₐ[K] L) : Shrink.{0} L ≃ₐ[Shrink.{0} K] Shrink.{0} L :=
  AlgEquiv.ofRingEquiv (f := ((eqv L).symm.trans (σ : L ≃+* L)).trans (eqv L)) (fun x => by
    obtain ⟨k, rfl⟩ := (eqv K).surjective x
    show eqv L (σ ((eqv L).symm (algebraMap _ _ (eqv K k)))) = _
    rw [algebraMap_eqv, RingEquiv.symm_apply_apply, AlgEquiv.commutes])

end models
end
end P2mS26UnivA
end P2MW.S_M4aHerbrand_infiniteIdeleFibre_tateCard_eq_localDegreeProd
