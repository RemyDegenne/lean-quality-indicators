public noncomputable section

open Function Set Equiv Order

open scoped Cardinal Ordinal

universe u v w

namespace Ordinal

@[simp]
theorem opow_eq_zero {a b : Ordinal} : a ^ b = 0 ↔ a = 0 ∧ b ≠ 0 := by
  by_cases a = 0 <;> by_cases b = 0 <;> simp_all [opow_ne_zero]

end Ordinal
end
