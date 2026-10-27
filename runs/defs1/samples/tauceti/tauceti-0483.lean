public section

namespace NumberField.Set

open Filter IsDedekindDomain

open scoped NumberField Topology

variable {K : Type*} [Field K] [NumberField K]

variable {S T : Set (HeightOneSpectrum (𝓞 K))} {δ ε : ℝ}

/-- A set `S` of height-one primes of a number field has natural density `δ` when the proportion
of primes of `S` below `x`, relative to all primes below `x`, tends to `δ` as `x → ∞`.

Both counts use the inclusive real cutoff fixed by `TauCeti.primeCount`. -/
def HasNaturalDensity (S : Set (HeightOneSpectrum (𝓞 K))) (δ : ℝ) : Prop :=
  Tendsto (fun x : ℝ => TauCeti.primeCount K S x /
    TauCeti.primeCount K (Set.univ : Set (HeightOneSpectrum (𝓞 K))) x) atTop (𝓝 δ)

end NumberField.Set
end
