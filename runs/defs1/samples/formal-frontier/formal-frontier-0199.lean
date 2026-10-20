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

/-- Restriction of continuous crossed homomorphisms to an open subgroup.
Its value on subgroup elements is computed by evaluation in the ambient group. -/
@[expose]
def crossedRestrict (H : OpenSubgroup G) :
    continuousCrossedHom X →L[k]
      continuousCrossedHom (TopRep.res H.subtype X) :=
  ((ContinuousMap.compCLM k X
      ⟨H.subtype, continuous_subtype_val⟩).comp
        (Submodule.subtypeL (continuousCrossedHom X))).codRestrict
    (continuousCrossedHom (TopRep.res H.subtype X)) fun f g h => by
      change f.1 (((g * h : H) : G)) = X.ρ (g : G) (f.1 (h : G)) + f.1 (g : G)
      exact f.2 (g : G) (h : G)

end CorestrictionTransversal
end
end ContinuousCohomology
end
