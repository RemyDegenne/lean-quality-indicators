@[expose] public section

namespace TensorProduct

namespace AlgebraTensorModule

universe uR uS uA uB uM uN uP uQ uP' uQ'

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ} {P' : Type uP'} {Q' : Type uQ'}

open LinearMap

open Algebra (lsmul)

section Semiring

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

variable [AddCommMonoid M] [Module R M] [Module A M]

variable [IsScalarTower R A M]

variable [AddCommMonoid N] [Module R N]

variable [AddCommMonoid P] [Module R P] [Module A P]

variable [IsScalarTower R A P]

variable [AddCommMonoid Q] [Module R Q]

variable [AddCommMonoid P'] [Module R P'] [Module A P']

variable [IsScalarTower R A P']

variable [AddCommMonoid Q'] [Module R Q']

variable (R A B M N P Q)

section

variable [Module B P] [IsScalarTower R B P] [SMulCommClass A B P]

variable {R A B M N P Q}

@[simp] lemma lTensor_tmul (f : N →ₗ[R] Q) (m : M) (n : N) :
    lTensor A M f (m ⊗ₜ[R] n) = m ⊗ₜ f n :=
  rfl

end
end Semiring
end AlgebraTensorModule
end TensorProduct
end
