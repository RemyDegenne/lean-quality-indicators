public section

set_option warningAsError true

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

open scoped Pointwise

/-- First isomorphism with the native integer submodule and quotient types. -/
noncomputable def principalIntLinearQuotientEquiv (a : ℤ) (ha : IsRegular a) (k : ℕ) :
    (adicallyRestrictedSubring (σ := σ) (Ideal.span ({a} : Set ℤ)) ⧸
      ((Ideal.span ({a} : Set ℤ)) ^ k •
        (⊤ : Submodule ℤ
          (adicallyRestrictedSubring (σ := σ) (Ideal.span ({a} : Set ℤ)))))) ≃ₗ[ℤ]
      MvPolynomial σ (ℤ ⧸ (Ideal.span ({a} : Set ℤ)) ^ k) :=
  (Submodule.quotEquivOfEq _ _
    (ker_intLinearAdicReduction_principal (σ := σ) a ha k).symm).trans
      ((intLinearAdicReduction (σ := σ) (Ideal.span ({a} : Set ℤ)) k).quotKerEquivOfSurjective
        (intLinearAdicReduction_surjective (σ := σ) (Ideal.span ({a} : Set ℤ)) k))

end MvPowerSeries
end
