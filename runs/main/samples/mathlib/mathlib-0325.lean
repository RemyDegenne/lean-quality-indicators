@[expose] public section

universe u

open scoped PowerSeries

open HahnSeries Polynomial

noncomputable section

variable {R : Type*}

namespace LaurentSeries

section Semiring

variable [Semiring R]

@[simp]
theorem coeff_coe_powerSeries (x : R⟦X⟧) (n : ℕ) :
    HahnSeries.coeff (x : R⸨X⸩) n = PowerSeries.coeff n x := by
  rw [ofPowerSeries_apply_coeff]

end Semiring
end LaurentSeries
end
end
