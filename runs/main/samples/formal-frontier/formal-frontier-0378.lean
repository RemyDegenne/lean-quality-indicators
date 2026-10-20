public section

set_option warningAsError true

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

section ValuationDomain

variable [IsDomain R] [ValuationRing R]

@[simp]
theorem restrictedResidue_polynomial (a : R)
    (ham : a ∈ IsLocalRing.maximalIdeal R) (p : MvPolynomial σ R) :
    restrictedResidue a ham (polynomialToRestricted (Ideal.span {a}) p) =
      MvPolynomial.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)) p := by
  rw [← restrictedResidueHom_apply]
  exact reductionAtLargerIdeal_polynomial _ _ _ p

end ValuationDomain
end MvPowerSeries
end
