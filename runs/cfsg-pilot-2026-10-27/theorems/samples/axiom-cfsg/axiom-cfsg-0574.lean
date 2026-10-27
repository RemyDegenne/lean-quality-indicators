public section

namespace CFSG.Sporadic.Th.Kernel

open CFSG.Sporadic.Bridge CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th.Max3 TauCeti Pointwise
  MulAction

variable (h : KernelFacts)

include h

theorem orderOf_a : orderOf a = 2 :=
  orderOf_eq_prime (by rw [sq]; exact a_mul_a) (a_ne_one h)

end CFSG.Sporadic.Th.Kernel
end
