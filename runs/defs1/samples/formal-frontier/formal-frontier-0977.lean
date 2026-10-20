set_option autoImplicit false

public section

open CategoryTheory

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace ContinuousCohomology

noncomputable section

namespace CorestrictionTransversal

variable {H : Subgroup G} (T : H.RightTransversal)

variable (X : TopRep.{max v w} k G)

noncomputable local instance transversalFintype (H : OpenSubgroup G)
    [H.toSubgroup.FiniteIndex] (T : H.toSubgroup.RightTransversal) :
    Fintype ↥(T : Set G) :=
  T.2.finite_right.fintype

/-- The identity coefficient map comparing restriction along the continuous
inclusion with the representation restricted along the underlying subgroup
inclusion. -/
def restrictionCoeffHom (H : OpenSubgroup G) :
    TopRep.res (openSubgroupInclusion H : H →* G) X ⟶
      TopRep.res H.subtype X :=
  TopRep.ofHom {
    __ := ContinuousLinearMap.id k X
    isIntertwining' := by intro h; rfl }

end CorestrictionTransversal
end
end ContinuousCohomology
end
