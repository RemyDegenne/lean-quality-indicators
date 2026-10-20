@[expose] public section

variable {R S A B : Type*}

open MulOpposite

section Semiring

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S A] [SMulCommClass R S A]

variable [IsScalarTower R S A]

namespace AlgHom

/--
An algebra homomorphism `f : A →ₐ[R] B` such that `f x` commutes with `f y` for all `x, y` defines
an algebra homomorphism from `Aᵐᵒᵖ`. -/
@[simps -fullyApplied]
def fromOpposite (f : A →ₐ[R] B) (hf : ∀ x y, Commute (f x) (f y)) : Aᵐᵒᵖ →ₐ[R] B :=
  { f.toRingHom.fromOpposite hf with
    toFun := f ∘ unop
    commutes' := fun r => f.commutes r }

end AlgHom
end Semiring
end
