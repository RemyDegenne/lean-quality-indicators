open scoped Finset

@[expose] public section

section

open Pointwise

namespace Semigroup

variable {M M' : Type*} [Mul M] [Mul M'] (f : M →ₙ* M')

variable (M) in
@[to_additive]
theorem exists_finite_of_isMulFG [IsMulFG M] : ∃ S : Set M, S.Finite ∧ Subsemigroup.closure S = ⊤ :=
  isMulFG_iff_finite.mp ‹_›

end Semigroup
end
end
