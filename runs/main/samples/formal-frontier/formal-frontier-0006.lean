public section

open DirectSum

namespace GradedLocalization

universe u v w

variable {A : Type u} [CommRing A]

variable {ι : Type v} [DecidableEq ι] [AddCommGroup ι]

variable {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A]

variable (𝒜 : ι → σ) [GradedRing 𝒜]

variable (M : Submonoid A)

theorem mk_mem_component {i j : ι} (a : 𝒜 (i + j)) (b : 𝒜 j)
    (hb : (b : A) ∈ M) :
    Localization.mk (a : A) ⟨(b : A), hb⟩ ∈ component (𝒜 := 𝒜) M i :=
  ⟨j, a, b, hb, rfl⟩

end GradedLocalization
end
