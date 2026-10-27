@[expose] public section

namespace AlgebraicGeometry.Proj

open HomogeneousLocalization CategoryTheory

universe u

variable {σ : Type*} {A : Type u}

variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]

variable (𝒜 : ℕ → σ)

variable [GradedRing 𝒜]

section basicOpen

variable (f g : A)

/-- The structure map `Proj A ⟶ Spec A₀`. -/
noncomputable
def toSpecZero : Proj 𝒜 ⟶ Spec ↧(𝒜 0) :=
  (Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ (basicOpen_one _)).inv ≫
    basicOpenToSpec 𝒜 1 ≫ Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 _))

end basicOpen
end AlgebraicGeometry.Proj
end
