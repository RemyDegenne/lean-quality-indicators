public section

namespace TauCeti

open NumberField IsDedekindDomain nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

namespace UnitaryIdealWeight

/-- Restricting a unitary weight away from a finite set of primes keeps it unitary: the
restricted weight is unchanged at the primes that are good for it. -/
noncomputable def restrictAway (χ : UnitaryIdealWeight K) (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : S.Finite) : UnitaryIdealWeight K :=
  ⟨χ.1.restrictAway S hS, fun 𝔭 h𝔭 ↦ by
    rw [MultiplicativeIdealWeight.badPrimes_restrictAway, Set.mem_union, not_or] at h𝔭
    rw [MultiplicativeIdealWeight.restrictAway_apply]
    simp [h𝔭.2, χ.2 𝔭 h𝔭.1]⟩

end UnitaryIdealWeight
end TauCeti
end
