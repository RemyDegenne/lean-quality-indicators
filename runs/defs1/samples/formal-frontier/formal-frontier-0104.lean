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

/-- The coefficient measuring the change from `T` to `S`. -/
noncomputable def changeCoefficient (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    (T S : H.toSubgroup.RightTransversal)
    (f : continuousCrossedHom (TopRep.res H.subtype X)) : X :=
  ∑ t : ↥(T : Set G),
    X.ρ ((t : G)⁻¹) (f.1 (changeFactor T S t))

end CorestrictionTransversal
end
end ContinuousCohomology
end
