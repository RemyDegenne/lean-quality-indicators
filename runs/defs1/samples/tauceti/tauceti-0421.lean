public section

namespace TauCeti

open Filter NumberField

open scoped Asymptotics nonZeroDivisors NumberField

open IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

variable {S : Set (HeightOneSpectrum (𝓞 K))} {x δ : ℝ}

variable (K) in
/-- The **von Mangoldt weight of a set `S` of height-one primes**, as a real weight on the nonzero
integral ideals of `𝓞 K`: the value `log N(𝔭)` at `𝔭 ^ k` for `𝔭 ∈ S` and `k ≥ 1`, and `0` at every
other nonzero ideal.

It is the ideal von Mangoldt function of Layer 2 cut down to the prime powers whose base lies in
`S`, taken in its real form, because the Tauberian input of Layer 9 is a nonnegative *real*
coefficient system.  Cutting down by "some prime of `S` divides `A`" rather than by the prime base
of `A` avoids naming that base at ideals which are not prime powers, where the ideal von Mangoldt
function vanishes anyway. -/
noncomputable def primeVonMangoldtWeight (S : Set (HeightOneSpectrum (𝓞 K)))
    (A : (Ideal (𝓞 K))⁰) : ℝ :=
  {I : (Ideal (𝓞 K))⁰ | ∃ 𝔭 ∈ S, 𝔭.asIdeal ∣ (I : Ideal (𝓞 K))}.indicator
    (fun I ↦ (IdealArithmeticFunction.vonMangoldt I).re) A

end TauCeti
end
