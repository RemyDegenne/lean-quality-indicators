@[expose] public section

open scoped TensorProduct

open TensorProduct

namespace Algebra

namespace TensorProduct

universe uR uS uA uB uC uD uE uF

variable {R : Type uR} {R' : Type*} {S : Type uS} {T : Type*}

variable {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} {E : Type uE} {F : Type uF}

section Monoidal

section

variable [CommSemiring R] [CommSemiring S] [Algebra R S]

variable [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

variable [Semiring B] [Algebra R B]

variable [Semiring C] [Algebra S C]

variable [Semiring D] [Algebra R D]

@[simp]
theorem algHomOfLinearMapTensorProduct_apply (f h_mul h_one x) :
    (algHomOfLinearMapTensorProduct f h_mul h_one : A ⊗[R] B →ₐ[S] C) x = f x :=
  rfl

end
end Monoidal
end TensorProduct
end Algebra
end
