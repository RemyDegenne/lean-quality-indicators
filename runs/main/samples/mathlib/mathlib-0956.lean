@[expose] public section

variable {α : Type*}

namespace Nonneg

section LinearOrder

variable [Zero α] [LinearOrder α]

@[simp]
theorem toNonneg_lt {a : Nonneg α} {b : α} : a < toNonneg b ↔ ↑a < b := by
  obtain ⟨a, ha⟩ := a
  simp [toNonneg, ha.not_gt]

end LinearOrder
end Nonneg
end
