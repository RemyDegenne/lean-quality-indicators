public section

set_option warningAsError true

namespace MonomialOrder

open MvPowerSeries

variable {σ R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]

theorem restrictedResidue_support_eq_of_unit_factor
    (a : R) (ham : a ∈ IsLocalRing.maximalIdeal R)
    (z h : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))
    (c : R) (hc : IsUnit c)
    (hfactor : (z : MvPowerSeries σ R) = C c * (h : MvPowerSeries σ R)) :
    (restrictedResidue a ham z).support = (restrictedResidue a ham h).support := by
  obtain ⟨v, hv⟩ := isUnit_iff_dvd_one.mp hc
  have hcoeff (d : σ →₀ ℕ) :
      coeff d (z : MvPowerSeries σ R) = c * coeff d (h : MvPowerSeries σ R) := by
    rw [hfactor, coeff_C_mul]
  have hcoeff' (d : σ →₀ ℕ) :
      coeff d (h : MvPowerSeries σ R) = v * coeff d (z : MvPowerSeries σ R) := by
    calc
      coeff d (h : MvPowerSeries σ R) = (1 : R) * coeff d (h : MvPowerSeries σ R) :=
        (one_mul _).symm
      _ = (c * v) * coeff d (h : MvPowerSeries σ R) := by rw [← hv]
      _ = v * (c * coeff d (h : MvPowerSeries σ R)) := by
        rw [mul_comm c v, mul_assoc]
      _ = v * coeff d (z : MvPowerSeries σ R) := by rw [hcoeff]
  have hscale (d : σ →₀ ℕ) :
      (restrictedResidue a ham z).coeff d =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) c *
          (restrictedResidue a ham h).coeff d := by
    simp only [coeff_restrictedResidue, hcoeff, map_mul]
  have hscale' (d : σ →₀ ℕ) :
      (restrictedResidue a ham h).coeff d =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) v *
          (restrictedResidue a ham z).coeff d := by
    simp only [coeff_restrictedResidue, hcoeff', map_mul]
  apply Finset.ext
  intro d
  simp only [MvPolynomial.mem_support_iff]
  constructor
  · intro hd hzero
    apply hd
    rw [hscale d, hzero, mul_zero]
  · intro hd hzero
    apply hd
    rw [hscale' d, hzero, mul_zero]

end MonomialOrder
end
