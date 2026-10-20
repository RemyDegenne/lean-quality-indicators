public section

namespace GradedAlgebra

universe u v

variable {A : Type u} [CommRing A]

variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]

variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem isNoetherianRing_of_gradeZero_of_irrelevant_fg
    [IsNoetherianRing (𝒜 0)]
    (h : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG) :
    IsNoetherianRing A := by
  let _ : Algebra.FiniteType (𝒜 0) A := finiteType_of_irrelevant_fg 𝒜 h
  exact Algebra.FiniteType.isNoetherianRing (𝒜 0) A

end GradedAlgebra
end
