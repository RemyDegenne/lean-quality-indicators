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

/-- The degree-one corestriction morphism determined by a right transversal.
Its crossed-quotient formula is used by the composition and Mackey laws. -/
@[expose]
noncomputable def corestrictionOneWithTransversal
    (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    (T : H.toSubgroup.RightTransversal) [TopRep.JointlyContinuous X]
    [LocallyCompactSpace G] [LocallyCompactSpace H] :
    continuousCohomology 1 (TopRep.res H.subtype X) ⟶ continuousCohomology 1 X :=
  (degreeOneIso (TopRep.res H.subtype X)).inv ≫
    TopModuleCat.ofHom (transferQuotient X H T) ≫
      (degreeOneIso X).hom

end CorestrictionTransversal
end
end ContinuousCohomology
end
