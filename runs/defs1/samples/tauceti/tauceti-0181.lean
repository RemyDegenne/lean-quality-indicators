public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped nonZeroDivisors

namespace IsDedekindDomain.FiniteAdeleRing

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The invertible fractional ideal `∏_v v ^ ord_v(x)` attached to a finite idele `x`. -/
noncomputable def toFractionalIdeal : 𝔸ᶠ[R, K]ˣ →* (FractionalIdeal R⁰ K)ˣ where
  toFun x := ∏ᶠ v : HeightOneSpectrum R, v.unitOfPrime K ^ adicOrd x v
  map_one' := by simp only [adicOrd_one, zpow_zero, finprod_one]
  map_mul' x y := by
    simp only [adicOrd_mul, zpow_add]
    exact finprod_mul_distrib (hasFiniteMulSupport_unitOfPrime_zpow_adicOrd x)
      (hasFiniteMulSupport_unitOfPrime_zpow_adicOrd y)

end IsDedekindDomain.FiniteAdeleRing
end
