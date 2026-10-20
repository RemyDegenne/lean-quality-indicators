@[expose] public section

universe uι u v

open Algebra Set MulOpposite

open scoped Pointwise

namespace Submodule

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

scoped[Pointwise] attribute [instance] Submodule.hasDistribPointwiseNeg

scoped[Pointwise] attribute [instance] Submodule.pointwiseMulSemiringAction

section AlgebraCommSemiring

variable {A : Type v} [CommSemiring A] [Algebra R A]

variable {M N : Submodule R A} {m n : A}

variable (M N)

protected theorem mul_comm : M * N = N * M :=
  le_antisymm (mul_le.2 fun _r hrm _s hsn => mul_mem_mul_rev hsn hrm)
    (mul_le.2 fun _r hrn _s hsm => mul_mem_mul_rev hsm hrn)

end AlgebraCommSemiring
end Submodule
end
