public section

open Function Set Cardinal Equiv Order Ordinal

universe u v w

namespace Cardinal

section add

theorem add_eq_max' {a b : Cardinal} (ha : ℵ₀ ≤ b) : a + b = max a b := by
  rw [add_comm, max_comm, add_eq_max ha]

end add
end Cardinal
end
