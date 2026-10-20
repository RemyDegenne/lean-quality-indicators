@[expose] public section

set_option warningAsError true

namespace AlgebraicGeometry.Proj

open CategoryTheory Limits HomogeneousLocalization TopologicalSpace

universe u

variable {σ : Type*} {A : Type u}

variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]

variable (𝒜 : ℕ → σ) [GradedRing 𝒜] {X : Scheme.{u}}

variable (f : A →+* Γ(X, ⊤))

/-- The geometric cover by positive-degree homogeneous basic opens. -/
def openCoverOfGlobalSectionsOfIsOpenCover
    (hcover : IsOpenCover (fun ir : Σ' i r, 0 < i ∧ r ∈ 𝒜 i ↦
      X.basicOpen (f ir.2.1))) : X.OpenCover :=
  X.openCoverOfIsOpenCover _ hcover

end AlgebraicGeometry.Proj
end
