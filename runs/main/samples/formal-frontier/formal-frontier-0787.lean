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

omit [IsTopologicalGroup G] in
lemma crossedRestrict_comp_mkQL (H : OpenSubgroup G)
    [TopRep.JointlyContinuous X] :
    TopModuleCat.ofHom (crossedRestrict X H) ≫
        TopModuleCat.ofHom
          (principalCocycles (TopRep.res H.subtype X)).mkQL =
      TopModuleCat.ofHom (principalCocycles X).mkQL ≫
        TopModuleCat.ofHom (crossedQuotientRestrict X H) := by
  ext f
  rfl

end CorestrictionTransversal
end
end ContinuousCohomology
end
