set_option autoImplicit false

set_option warningAsError true

public section

open CategoryTheory

noncomputable section

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace ContinuousCohomology

namespace CorestrictionTransversal

variable (X : TopRep.{max v w} k G)

attribute [local instance] jointlyContinuous_mackeyStabilizer

variable (X : TopRep.{max v w} k G)

lemma crossedRestrict_transferCrossed_mackey (H K : OpenSubgroup G)
    [H.toSubgroup.FiniteIndex]
    (T : (q : DoubleCoset.Quotient (H : Set G) K) ->
      (mackeyOpenStabilizer H K q.out).toSubgroup.RightTransversal)
    (f : continuousCrossedHom (TopRep.res H.subtype X)) :
    crossedRestrict X K
        (transferCrossed X H (mackeyAssembledRightTransversal H K T) f) =
      mackeyCrossedSumWithTransversal X H K T f := by
  ext g
  exact transferCrossed_mackey_apply X H K T f g

end CorestrictionTransversal
end ContinuousCohomology
end
end
