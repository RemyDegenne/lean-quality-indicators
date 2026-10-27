namespace HomogeneousIdealQuotientGrading

open DirectSum

section Engine

variable {ι A σ τ : Type*}

variable [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ)

variable (I : Ideal A)

variable [SetLike τ (A ⧸ I)] [AddSubmonoidClass τ (A ⧸ I)] (ℬ : ι → τ)

variable [DecidableEq ι]

variable [AddMonoid ι] [GradedRing 𝒜]

def quotDecompose (hmem : ∀ (i : ι) (a : A), a ∈ 𝒜 i → Ideal.Quotient.mk I a ∈ ℬ i)
    (hI : I.IsHomogeneous 𝒜) : A ⧸ I →+ ⨁ i, ℬ i :=
  QuotientAddGroup.lift I.toAddSubgroup (preDecompose 𝒜 I ℬ hmem)
    (fun _ ha => preDecompose_eq_zero_of_mem 𝒜 I ℬ hmem hI ha)

end Engine
end HomogeneousIdealQuotientGrading
