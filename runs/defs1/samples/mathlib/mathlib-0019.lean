@[expose] public section

noncomputable section

open Finsupp Finset Function

namespace MvPowerSeries

section CommSemiring

variable {σ R : Type*} [CommSemiring R]

section optionEquivLeft

variable (R σ) in
/-- The algebra isomorphism between multivariable power series in `Option σ` and
  power series with coefficients in `MvPowerSeries σ R`. -/
@[no_expose]
def optionEquivLeft : MvPowerSeries (Option σ) R ≃ₐ[R] PowerSeries (MvPowerSeries σ R) where
  toFun := optionFunLeft σ R
  invFun := optionInvFunLeft σ R
  left_inv _ := by ext; simp [coeff_optionInvFunLeft, coeff_coeff_optionFunLeft]
  right_inv _ := by ext; simp [coeff_optionInvFunLeft, coeff_coeff_optionFunLeft]
  map_mul' := optionFunLeft_mul
  map_add' _ _ := by ext; simp [coeff_coeff_optionFunLeft]
  commutes' := by
    simpa [MvPowerSeries.algebraMap_apply, PowerSeries.C] using
      optionFunLeft_monomial (0 : Option σ →₀ ℕ)

end optionEquivLeft
end CommSemiring
end MvPowerSeries
end
end
