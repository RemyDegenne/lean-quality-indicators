@[expose] public section

universe uι uR uS uM uN

namespace ModuleCat

namespace FiniteProjective

section Prod

variable (R : Type uR) (S : Type uS) [Ring R] [Ring S]

variable (M : FiniteProjective.{uR, uM} Rᵐᵒᵖ) (N : FiniteProjective.{uS, uN} Sᵐᵒᵖ)

theorem prodRightMk_apply (m : M) (n : N) :
    prodRightMk R S M N m n = (m, n) := by
  rfl

end Prod
end FiniteProjective
end ModuleCat
end
