public section

set_option warningAsError true

namespace MonomialOrder

open MvPowerSeries

variable {σ R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]

/-- The leading term is a polynomial monomial with the *actual* `R`-valued
coefficient of the series, not its residue coefficient. Zero has term zero. -/
noncomputable def restrictedLeadingTerm (μ : MonomialOrder σ) (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    (z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) : MvPolynomial σ R := by
  classical
  exact if z = 0 then 0 else
    MvPolynomial.monomial (μ.restrictedLeadingExponent a ham z)
      (coeff (μ.restrictedLeadingExponent a ham z) (z : MvPowerSeries σ R))

end MonomialOrder
end
