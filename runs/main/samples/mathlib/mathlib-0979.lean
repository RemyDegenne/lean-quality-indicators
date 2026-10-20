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

@[simp, norm_cast]
theorem coe_toMonoidHom (f : A →ₐ[R] B) : ⇑(f : A →* B) = f :=
  rfl

end Semiring
end AlgHom
end
