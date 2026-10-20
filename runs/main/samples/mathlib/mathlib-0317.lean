public noncomputable section

open Function Cardinal Set Order

open scoped Ordinal

universe u v w

variable {α γ : Type u} {β : Type v}

namespace Ordinal

theorem cof_eq_one_iff {o} : cof o = 1 ↔ o ∈ range succ := by
  cases o using inductionOnWellOrder with | type α
  rw [cof_type, Order.cof_eq_one_iff, type_lt_mem_range_succ_iff]
  simp_rw [isTop_iff_isMax]

end Ordinal
end
