public section

open DirectSum

namespace GradedLocalization

universe u v w

variable {A : Type u} [CommRing A]

variable {ι : Type v} [DecidableEq ι] [AddCommGroup ι]

variable {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A]

variable (𝒜 : ι → σ) [GradedRing 𝒜]

variable (M : Submonoid A)

variable (hM : M ≤ SetLike.homogeneousSubmonoid 𝒜)

include hM in
theorem isInternal : DirectSum.IsInternal (component (𝒜 := 𝒜) M) :=
  ⟨coe_injective 𝒜 M hM, coe_surjective 𝒜 M hM⟩

end GradedLocalization
end
