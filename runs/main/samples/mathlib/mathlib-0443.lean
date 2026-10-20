@[expose] public section

open TensorProduct Coalgebra

universe u v w

@[inherit_doc CoalgHom]
infixr:25 " →ₗc " => CoalgHom _

@[inherit_doc]
notation:25 A " →ₗc[" R "] " B => CoalgHom R A B

namespace CoalgHom

variable {R A B C D : Type*}

section

variable [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
  [AddCommMonoid C] [Module R C] [AddCommMonoid D] [Module R D]
  [CoalgebraStruct R A] [CoalgebraStruct R B] [CoalgebraStruct R C] [CoalgebraStruct R D]

@[ext high]
theorem ext_of_ring {f g : R →ₗc[R] A} (h : f 1 = g 1) : f = g :=
  linearMapOfClass_injective (by ext; assumption)

end
end CoalgHom
end
