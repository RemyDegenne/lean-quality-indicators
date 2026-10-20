@[expose] public section

universe u

open scoped WithZero

namespace LaurentSeries

variable (K : Type u) [Field K]

theorem mem_powerSeries_as_subring_iff (x : LaurentSeries K) :
    x ∈ powerSeries_as_subring K ↔ (Valued.v x : ℤᵐ⁰) ≤ 1 := by
  rw [val_le_one_iff_eq_coe K x]
  simp only [powerSeries_as_subring, Subring.mem_map, Subring.mem_top, true_and]

end LaurentSeries
end
