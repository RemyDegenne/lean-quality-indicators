@[expose] public section

open AlgebraicGeometry

namespace AlgebraicGeometry.Proj

universe u v

variable {A : Type u} [CommRing A]

variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]

variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The projective basic opens associated to positive-degree homogeneous
elements. -/
def positiveBasicOpens : Set (Set (Proj 𝒜)) :=
  Set.range fun i : Σ n : PNat, 𝒜 (n : ℕ) =>
    (Proj.basicOpen 𝒜 (i.2 : A) : Set (Proj 𝒜))

end AlgebraicGeometry.Proj
end
