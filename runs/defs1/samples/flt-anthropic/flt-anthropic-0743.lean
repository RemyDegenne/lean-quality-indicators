set_option autoImplicit false

noncomputable section

namespace IsDedekindDomain.selmerGroup

open IsDedekindDomain FractionalIdeal

open scoped nonZeroDivisors Classical

variable {R : Type} [CommRing R] [IsDedekindDomain R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
  (S : Set (HeightOneSpectrum R)) (n : ℕ)

def radClass (x : Kˣ) : ClassGroupModS S := QuotientGroup.mk (ClassGroup.mk K (Units.mk0 (rad K S n x) (rad_ne_zero K S n x)))

end IsDedekindDomain.selmerGroup
end
