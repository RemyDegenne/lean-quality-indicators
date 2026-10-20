public section

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]

theorem isUnit_adicallyRestricted_iff_coeff_radical
    (f : adicallyRestrictedSubring (σ := σ) I) :
    IsUnit f ↔ IsUnit (coeff 0 (f : MvPowerSeries σ R)) ∧
      ∀ α : σ →₀ ℕ, α ≠ 0 → coeff α (f : MvPowerSeries σ R) ∈ I.radical := by
  rw [isUnit_adicallyRestricted_iff_coeff_mod_ideal I f]
  simp only [← isUnit_iff_quotient_of_isAdicComplete I,
    IsNilpotent, ← map_pow, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_radical_iff]

end MvPowerSeries
end
