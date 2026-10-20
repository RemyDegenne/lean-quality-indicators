@[expose] public section

universe uR uS

namespace ModuleCat.RightExtension

variable {R : Type uR} {S : Type uS}

section PrincipalIdeal

variable [Ring R] [Ring S] (f : R →+* S) (e : R)

/-- Restrict the opposite homomorphism to the principal right ideal. -/
def spanSemilinear :
    Ideal.span {MulOpposite.op e} →ₛₗ[RingHom.op f] Sᵐᵒᵖ where
  toFun m := RingHom.op f m.val
  map_add' m n := (RingHom.op f).map_add m.val n.val
  map_smul' r m := (RingHom.op f).map_mul r m.val

end PrincipalIdeal
end ModuleCat.RightExtension
end
