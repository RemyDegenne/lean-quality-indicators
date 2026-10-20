@[expose] public section

namespace ComputableℝSeq

open scoped QInterval

section simps

variable (x y : ComputableℝSeq)

theorem lb_mul : (x * y).lb = ((x.lb * y.lb) ⊓ (x.ub * y.lb)) ⊓ ((x.lb * y.ub) ⊓ (x.ub * y.ub)) :=
  by
  ext
  rw [← mulLb, ← fst_mul'_eq_mulLb]
  rfl

end simps
end ComputableℝSeq
end
