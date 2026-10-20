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

/-- The finite sum of the quotient-level summands over `H \ G / K`. -/
noncomputable def mackeyDoubleCosetSum
    (H K : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    [TopRep.JointlyContinuous X] :
    (continuousCrossedHom (TopRep.res H.subtype X) ⧸
        principalCocycles (TopRep.res H.subtype X)) →L[k]
      (continuousCrossedHom (TopRep.res K.subtype X) ⧸
        principalCocycles (TopRep.res K.subtype X)) := by
  let _ : Fintype (DoubleCoset.Quotient (H : Set G) K) := Fintype.ofFinite _
  exact ∑ q : DoubleCoset.Quotient (H : Set G) K,
    mackeyDoubleCosetSummand X H K q

end CorestrictionTransversal
end ContinuousCohomology
end
end
