@[expose] public section

universe uι uR uS uM uN

namespace ModuleCat

namespace FiniteProjective

section Prod

variable (R : Type uR) (S : Type uS) [Ring R] [Ring S]

variable (M : FiniteProjective.{uR, uM} Rᵐᵒᵖ) (N : FiniteProjective.{uS, uN} Sᵐᵒᵖ)

/-- The binary finite-projective carrier comparison is the identity on pairs. -/
def prodRightLinearEquiv : prodRight R S M N ≃ₗ[(R × S)ᵐᵒᵖ]
    ModuleCat.prodRight R S M.obj N.obj :=
  LinearEquiv.refl (R × S)ᵐᵒᵖ (ModuleCat.prodRight R S M.obj N.obj)

end Prod
end FiniteProjective
end ModuleCat
end
