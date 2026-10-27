public section

open DirectSum

namespace GradedLocalization

universe u v w

variable {A : Type u} [CommRing A]

variable {ι : Type v} [DecidableEq ι] [AddCommGroup ι]

variable {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A]

variable (𝒜 : ι → σ) [GradedRing 𝒜]

variable (M : Submonoid A)

/-- The degree-zero localized component as a subring of the ordinary
localization. -/
@[expose] def zeroComponent : Subring (Localization M) where
  carrier := component (𝒜 := 𝒜) M 0
  zero_mem' := (component (𝒜 := 𝒜) M 0).zero_mem
  add_mem' := (component (𝒜 := 𝒜) M 0).add_mem
  neg_mem' := (component (𝒜 := 𝒜) M 0).neg_mem
  one_mem' := SetLike.one_mem_graded (component (𝒜 := 𝒜) M)
  mul_mem' {x y} hx hy := by
    change x * y ∈ component (𝒜 := 𝒜) M 0
    simpa only [zero_add] using
      (SetLike.GradedMul.mul_mem hx hy :
        x * y ∈ component (𝒜 := 𝒜) M (0 + 0))

end GradedLocalization
end
