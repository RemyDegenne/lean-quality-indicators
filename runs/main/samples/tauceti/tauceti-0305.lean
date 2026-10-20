public section

namespace TauCeti

open Filter

open scoped nonZeroDivisors NumberField

open IsDedekindDomain

variable (K : Type*) [Field K] [NumberField K]

variable {K}

variable (K)

variable {K}

variable (K)

variable {K}

variable {S T : Set (HeightOneSpectrum (𝓞 K))} {x : ℝ}

theorem primeTheta_eq_zero_of_lt_two (S : Set (HeightOneSpectrum (𝓞 K))) (hx : x < 2) :
    primeTheta K S x = 0 :=
  summatory_eq_zero_of_lt _ two_le_absNorm_asIdeal_real hx _

end TauCeti
end
