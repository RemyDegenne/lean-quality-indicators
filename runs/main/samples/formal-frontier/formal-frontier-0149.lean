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
theorem coe_surjective :
    Function.Surjective
      (DirectSum.coeAddMonoidHom (component (𝒜 := 𝒜) M)) := by
  intro x
  refine Localization.induction_on x fun c ↦ ?_
  obtain ⟨j, hcj⟩ := hM c.2.2
  exact mk_mem_range 𝒜 M c.1 c.2 hcj

end GradedLocalization
end
