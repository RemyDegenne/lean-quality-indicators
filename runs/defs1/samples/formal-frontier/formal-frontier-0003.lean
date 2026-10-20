@[expose] public section

universe uι uR uS uM uN

namespace ModuleCat

section Prod

variable (R : Type uR) (S : Type uS) [Ring R] [Ring S]

variable (M : ModuleCat.{uM} Rᵐᵒᵖ) (N : ModuleCat.{uN} Sᵐᵒᵖ)

/-- Second-coordinate evaluation is semilinear along the opposite second projection. -/
def prodRightSnd : prodRight R S M N →ₛₗ[RingHom.op (RingHom.snd R S)] N where
  toFun x := x.2
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro a x
    exact congrArg Prod.snd (prodRight_smul R S M N a.unop.1 a.unop.2 x)

end Prod
end ModuleCat
end
