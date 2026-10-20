@[expose] public section

open scoped TensorProduct

open TensorProduct

namespace Algebra

namespace TensorProduct

universe uR uS uA uB uC uD uE uF

variable {R : Type uR} {R' : Type*} {S : Type uS} {T : Type*}

variable {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} {E : Type uE} {F : Type uF}

section Monoidal

variable [CommSemiring R] [CommSemiring S] [Algebra R S]

variable [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

variable [Semiring B] [Algebra R B]

variable [Semiring C] [Algebra R C] [Algebra S C] [IsScalarTower R S C]

variable [Semiring D] [Algebra R D]

variable [Semiring E] [Algebra R E] [Algebra S E] [IsScalarTower R S E]

variable [Semiring F] [Algebra R F]

section

variable (R A)

variable (S)

section

variable [CommSemiring T] [Algebra R T] [Algebra S T]
    [Algebra T A] [IsScalarTower R T A] [IsScalarTower S T A]

variable (T C D) in
/-- The associator for tensor product of R-algebras, as an algebra isomorphism. -/
protected def assoc : (A ⊗[S] C) ⊗[R] D ≃ₐ[T] A ⊗[S] (C ⊗[R] D) :=
  AlgEquiv.ofLinearEquiv
    (AlgebraTensorModule.assoc R S T A C D)
    (by simp [Algebra.TensorProduct.one_def])
    ((LinearMap.map_mul_iff _).mpr <| by ext; simp)

end
end
end Monoidal
end TensorProduct
end Algebra
end
