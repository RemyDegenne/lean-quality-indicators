@[expose] public section

open GradedRing DirectSum SetLike Finset

variable {ι σ A : Type*}

variable [CommRing A]

variable [AddCommMonoid ι] [LinearOrder ι] [IsOrderedCancelAddMonoid ι]

variable [SetLike σ A] [AddSubmonoidClass σ A] {𝒜 : ι → σ} [GradedRing 𝒜]

theorem Ideal.IsHomogeneous.radical {I : Ideal A} (h : I.IsHomogeneous 𝒜) :
    I.radical.IsHomogeneous 𝒜 := by
  rw [h.radical_eq]
  exact Ideal.IsHomogeneous.sInf fun _ => And.left

end
