public section

set_option warningAsError true

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

@[simp]
theorem coeff_adicReduction (I : Ideal R) (k : ℕ)
    (f : adicallyRestrictedSubring (σ := σ) I) (m : σ →₀ ℕ) :
    (adicReduction I k f).coeff m =
      Ideal.Quotient.mk (I ^ k) (coeff m (f : MvPowerSeries σ R)) := by
  have hc := congrArg (MvPowerSeries.coeff m) (adicReduction_coe I k f)
  simpa only [MvPolynomial.coeff_coe, coeff_map] using hc

end MvPowerSeries
end
