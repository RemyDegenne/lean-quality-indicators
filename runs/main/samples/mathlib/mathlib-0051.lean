@[expose] public section

open TensorProduct Bialgebra Coalgebra Function

universe u v w

@[inherit_doc BialgHom]
infixr:25 " →ₐc " => BialgHom _

@[inherit_doc]
notation:25 A " →ₐc[" R "] " B => BialgHom R A B

namespace BialgHom

variable {R A B C D : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]

section AlgebraCoalgebra

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
  [CoalgebraStruct R A] [CoalgebraStruct R B] [CoalgebraStruct R C] [CoalgebraStruct R D]

variable (φ : A →ₐc[R] B)

theorem coe_fn_inj {φ₁ φ₂ : A →ₐc[R] B} : (φ₁ : A → B) = φ₂ ↔ φ₁ = φ₂ :=
  DFunLike.coe_fn_eq

end AlgebraCoalgebra
end BialgHom
end
