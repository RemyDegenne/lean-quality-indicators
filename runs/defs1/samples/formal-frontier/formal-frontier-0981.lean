public section

set_option warningAsError true

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

open scoped Pointwise

/-- Native first isomorphism for the regular principal ideal-power quotient. -/
noncomputable def principalLinearQuotientEquiv (a : R) (ha : IsRegular a) (k : ℕ) :
    (adicallyRestrictedSubring (σ := σ) (Ideal.span ({a} : Set R)) ⧸
      ((Ideal.span ({a} : Set R)) ^ k •
        (⊤ : Submodule R
          (adicallyRestrictedSubring (σ := σ) (Ideal.span ({a} : Set R)))))) ≃ₗ[R]
      MvPolynomial σ (R ⧸ (Ideal.span ({a} : Set R)) ^ k) :=
  (Submodule.quotEquivOfEq _ _
    (ker_linearAdicReduction_principal (σ := σ) a ha k).symm).trans
      ((linearAdicReduction (σ := σ) (Ideal.span ({a} : Set R)) k).quotKerEquivOfSurjective
        (linearAdicReduction_surjective (σ := σ) (Ideal.span ({a} : Set R)) k))

end MvPowerSeries
end
