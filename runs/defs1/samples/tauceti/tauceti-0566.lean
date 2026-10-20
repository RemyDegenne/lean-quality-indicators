public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped nonZeroDivisors

namespace IsDedekindDomain.FiniteAdeleRing

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

variable (R K) in
/-- The finite ideles that are units of the local integers at every place: the unit group of the
integral finite adeles `∏_v 𝒪_v`. -/
def integralUnits : Subgroup 𝔸ᶠ[R, K]ˣ where
  carrier := {x | ∀ v : HeightOneSpectrum R, Valued.v ((x : 𝔸ᶠ[R, K]) v) = 1}
  one_mem' v := by rw [Units.val_one, one_apply, map_one]
  mul_mem' hx hy v := by rw [Units.val_mul, mul_apply, map_mul, hx v, hy v, one_mul]
  inv_mem' {x} hx v := by rw [valued_coe_units_inv_apply, hx v, inv_one]

end IsDedekindDomain.FiniteAdeleRing
end
