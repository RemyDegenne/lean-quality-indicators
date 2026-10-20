@[expose] public section

universe uι uR uS uM uN

namespace ModuleCat

namespace FiniteProjective

section Prod

variable (R : Type uR) (S : Type uS) [Ring R] [Ring S]

variable (M : FiniteProjective.{uR, uM} Rᵐᵒᵖ) (N : FiniteProjective.{uS, uN} Sᵐᵒᵖ)

theorem prodRight_smul (r : R) (s : S) (x : prodRight R S M N) :
    MulOpposite.op (r, s) • x = (MulOpposite.op r • x.1, MulOpposite.op s • x.2) := by
  exact ModuleCat.prodRight_smul R S M.obj N.obj r s x

end Prod
end FiniteProjective
end ModuleCat
end
