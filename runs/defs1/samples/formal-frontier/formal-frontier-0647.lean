@[expose] public section

open Multiplicative WithZero

noncomputable section

namespace HomogeneousLocalization

variable {A ι σ : Type*} [CommRing A] [IsDomain A] [WfDvdMonoid A]

variable [SetLike σ A] [AddSubgroupClass σ A]

variable [AddCommMonoid ι] [DecidableEq ι]

variable (𝒜 : ι → σ) [GradedRing 𝒜]

variable {p : A}

/-- The prime-multiplicity valuation on the degree-zero homogeneous
localization away from a prime element. -/
noncomputable def awayPrimeMultiplicityValuation (hp : Prime p) :
    Valuation (Away 𝒜 p) ℤᵐ⁰ :=
  (PrimeMultiplicity.awayValuation
      (B := Localization.Away p) hp).comap
    (algebraMap (Away 𝒜 p) (Localization.Away p))

end HomogeneousLocalization
end
end
