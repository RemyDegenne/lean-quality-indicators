set_option autoImplicit false

public section

open CategoryTheory

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace ContinuousCohomology

variable (X : TopRep.{max v w} k G)

variable {A B C : TopRep.{max v w} k G}

noncomputable def cochainsZeroIso [TopRep.JointlyContinuous X] :
    (TopRep.homogeneousCochains X).X 0 ≅ TopModuleCat.of k X :=
  TopModuleCat.ofIso (cochainsZeroEquiv X)

end ContinuousCohomology
end
