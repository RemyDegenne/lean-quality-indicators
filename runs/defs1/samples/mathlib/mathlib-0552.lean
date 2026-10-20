public section

namespace Polynomial

variable {R : Type*}

section Semiring

variable [Semiring R]

/-- This says that `p` has `natDegree` `n` and is monic. -/
@[mk_iff isMonicOfDegree_iff']
structure IsMonicOfDegree (p : R[X]) (n : ℕ) : Prop where
  natDegree_eq : p.natDegree = n
  monic : p.Monic

end Semiring
end Polynomial
end
