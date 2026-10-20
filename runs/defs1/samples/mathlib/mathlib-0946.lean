@[expose] public section

open scoped TensorProduct

open TensorProduct

namespace Algebra

namespace TensorProduct

universe uR uS uA uB uC uD uE uF

variable {R : Type uR} {R' : Type*} {S : Type uS} {T : Type*}

variable {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} {E : Type uE} {F : Type uF}

section

variable [CommSemiring R] [Semiring A] [Semiring B] [CommSemiring S]

variable [Algebra R A] [Algebra R B] [Algebra R S]

variable (f : A →ₐ[R] S) (g : B →ₐ[R] S)

variable (R)

/-- `LinearMap.mul'` as an `AlgHom` over the algebra. -/
def lmul'' : S ⊗[R] S →ₐ[S] S :=
  algHomOfLinearMapTensorProduct
    { __ := LinearMap.mul' R S
      map_smul' := fun s x ↦ x.inductionOn
        (fun _ _ ↦ by simp [TensorProduct.smul_tmul', mul_assoc])
        fun x y hx hy ↦ by simp_all [mul_add] }
    (fun a₁ a₂ b₁ b₂ => by simp [mul_mul_mul_comm]) <| by simp

end
end TensorProduct
end Algebra
end
