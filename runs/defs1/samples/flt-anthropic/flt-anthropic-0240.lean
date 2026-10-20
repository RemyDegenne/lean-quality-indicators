set_option autoImplicit false

noncomputable section

open WithZero

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

section ToH1

def toH1Aux (S₀ S₁ : Set (Place K F)) (D : Divisor K F) : ↥(lSpaceOn (S₀ ∩ S₁) D) →ₗ[K] H1 D :=
  (repartitionsOf D ⊔ principalRepartitions K F).mkQ ∘ₗ extendOffChart K S₀ ∘ₗ
    (lSpaceOn (S₀ ∩ S₁) D).subtype

end ToH1
end AlgebraicCurve
end
