public section

set_option warningAsError true

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]

theorem restrictedResidue_ne_zero_of_coeff_one (a : R)
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    (h : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))
    (j : σ →₀ ℕ) (hj : coeff j (h : MvPowerSeries σ R) = 1) :
    restrictedResidue a ham h ≠ 0 := by
  let m : Ideal R := IsLocalRing.maximalIdeal R
  have hm : m ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  have hone : (Ideal.Quotient.mk m (1 : R)) ≠ 0 := by
    intro hzero
    exact hm ((Ideal.eq_top_iff_one m).mpr
      (Ideal.Quotient.eq_zero_iff_mem.mp hzero))
  intro hzero
  have hc := coeff_restrictedResidue a ham h j
  rw [hj, hzero] at hc
  exact hone (by simpa using hc.symm)

end MvPowerSeries
end
