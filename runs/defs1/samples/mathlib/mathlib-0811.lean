@[expose] public section

variable {R : Type*}

open MulOpposite

/-- A non-unital ring hom `R →ₙ+* S` can equivalently be viewed as a non-unital ring hom
`Rᵐᵒᵖ →+* Sᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps]
def NonUnitalRingHom.op {R S} [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] :
    (R →ₙ+* S) ≃ (Rᵐᵒᵖ →ₙ+* Sᵐᵒᵖ) where
  toFun f := { AddMonoidHom.mulOp f.toAddMonoidHom, MulHom.op f.toMulHom with }
  invFun f := { AddMonoidHom.mulUnop f.toAddMonoidHom, MulHom.unop f.toMulHom with }

end
