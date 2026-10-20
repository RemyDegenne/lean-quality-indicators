set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup

namespace BigWittLaw

open MvPolynomial

@[simp] theorem constantCoeff_killProd (k : ℕ) : PowerSeries.constantCoeff (killProd k) = 1 := by
  induction k with
  | zero => exact constantCoeff_genSeries
  | succ k ih =>
    rw [killProd_succ, map_mul, ih, one_mul, map_sub, map_one, map_mul, map_pow,
      PowerSeries.constantCoeff_X, zero_pow (Nat.succ_ne_zero k), mul_zero, sub_zero]

end BigWittLaw
end MvFormalGroup
end
