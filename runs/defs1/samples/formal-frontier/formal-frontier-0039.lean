@[expose] public section

set_option warningAsError true

namespace MonomialOrder

variable {σ ι R : Type*} [CommRing R] [Fintype ι]

variable (I : Ideal R) [IsAdicComplete I R]

variable (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)

variable (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))

variable (g : ι → MvPowerSeries.adicallyRestrictedSubring (σ := σ) I)

/-- Quotient coordinates for a finite family of restricted divisors, corrected
by the geometric inverse of the polynomial-division error. -/
noncomputable def restrictedPerturbedDivisionQuotient
    (hg : ∀ i, MvPowerSeries.adicReduction I 1
        (MvPowerSeries.polynomialToRestricted I (b i)) =
      MvPowerSeries.adicReduction I 1 (g i)) :
    MvPowerSeries.adicallyRestrictedSubring (σ := σ) I →ₗ[R]
      (ι → MvPowerSeries.adicallyRestrictedSubring (σ := σ) I) :=
  (restrictedDivisionQuotient I m b hb).comp
    (MvPowerSeries.restrictedGeometricInverse I
      (restrictedDivisionError I m b hb g)
      (restrictedDivisionError_raises I m b hb g hg))

end MonomialOrder
end
