@[expose] public section

set_option warningAsError true

noncomputable section

namespace AlgebraicGeometry.Proj

open CategoryTheory HomogeneousLocalization TopologicalSpace

universe u v w

variable {A B : Type u} {σ : Type v} {τ : Type w}

variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

variable [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  (ℬ : ℕ → τ) [GradedRing ℬ]

/-- An image distinguished open, indexed by a positive homogeneous source element. -/
def chartOpen (f : A →+* B) (i : Σ n : PNat, 𝒜 n) : (Proj ℬ).Opens :=
  basicOpen ℬ (f (i.2 : A))

end AlgebraicGeometry.Proj
end
end
