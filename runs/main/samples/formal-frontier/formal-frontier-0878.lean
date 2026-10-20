public section

set_option warningAsError true

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

@[simp]
theorem adicReduction_polynomial (I : Ideal R) (k : ℕ) (p : MvPolynomial σ R) :
    adicReduction I k (polynomialToRestricted I p) =
      MvPolynomial.map (Ideal.Quotient.mk (I ^ k)) p := by
  apply MvPolynomial.coe_injective σ (R ⧸ I ^ k)
  rw [adicReduction_coe, polynomialToRestricted_coe, map_polynomial_coe]

end MvPowerSeries
end
