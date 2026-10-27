@[expose] public section

universe u v w u₁ v₁

@[inherit_doc AlgHom]
infixr:25 " →ₐ " => AlgHom _

@[inherit_doc]
notation:25 A " →ₐ[" R "] " B => AlgHom R A B

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

section Semiring

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

variable (φ : A →ₐ[R] B)

/-- `AlgHom.toLinearMap` as a `MonoidHom`. -/
@[simps] def toEnd : (A →ₐ[R] A) →* Module.End R A where
  toFun := toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

end Semiring
end AlgHom
end
