public section

open scoped Pointwise

namespace CFSG.OddInversion

variable {G : Type*} [Group G]

theorem inv_eq_self_of_orderOf_eq_two {t : G} (ht : orderOf t = 2) : t⁻¹ = t := by
  rw [inv_eq_iff_mul_eq_one, ← sq, ← ht, pow_orderOf_eq_one]

end CFSG.OddInversion
end
