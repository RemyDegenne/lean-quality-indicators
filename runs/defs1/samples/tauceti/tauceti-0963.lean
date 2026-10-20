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

/-- The number of primes of `S` of absolute norm at most `x`, as a real number: the number-field
analogue of `π`. -/
noncomputable def primeCount (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) : ℝ :=
  primeSummatory K (S.indicator 1) x

end TauCeti
end
