public section

set_option warningAsError true

namespace MvPowerSeries

variable {R τ : Type*} [CommRing R] (I : Ideal R)

@[simp]
theorem restrictedFirstRegroup_polynomialRestrictedFirst
    (P : Polynomial (adicallyRestrictedSubring (σ := τ) I)) :
    restrictedFirstRegroup I (polynomialRestrictedFirst I P) =
      (P : PowerSeries (adicallyRestrictedSubring (σ := τ) I)) := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_restrictedFirstRegroup, restrictedFirstCoeff_polynomialRestrictedFirst,
    Polynomial.coeff_coe]

end MvPowerSeries
end
