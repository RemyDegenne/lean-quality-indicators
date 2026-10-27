public section

open DirectSum

namespace Ideal.Quotient

universe u v w

variable {A : Type u} [CommRing A]

variable {ι : Type v} [DecidableEq ι] [AddMonoid ι]

variable {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A]

variable (𝒜 : ι → σ) [GradedRing 𝒜]

variable (I : Ideal A)

/-- Decompose a quotient class into the images of its homogeneous components. -/
@[expose] def gradedDecompose (hI : I.IsHomogeneous 𝒜) :
    (A ⧸ I) →+ ⨁ i, gradedComponent 𝒜 I i :=
  QuotientAddGroup.lift (I : Submodule A A).toAddSubgroup
    (gradedDecomposePre 𝒜 I) (by
      intro x hx
      rw [AddMonoidHom.mem_ker]
      apply DirectSum.ext
      intro i
      apply Subtype.ext
      change Ideal.Quotient.mk I (GradedRing.proj 𝒜 i x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact (hI.mem_iff 𝒜).mp hx i)

end Ideal.Quotient
end
