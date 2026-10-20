set_option autoImplicit false

public section

open CategoryTheory

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace ContinuousCohomology

variable (X : TopRep.{max v w} k G)

variable {A B C : TopRep.{max v w} k G}

@[simp]
theorem cochainsZeroIso_hom_apply [TopRep.JointlyContinuous X]
    (σ : (TopRep.homogeneousCochains X).X 0) :
    (cochainsZeroIso X).hom.hom σ = σ.1 1 :=
  cochainsZeroEquiv_apply X σ

end ContinuousCohomology
end
