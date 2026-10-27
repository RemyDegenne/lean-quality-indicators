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

/-- The quotient-level Mackey summand attached to `x`, computed with a chosen
right transversal of its stabilizer in `K`. Its lift computes on cocycles. -/
@[expose]
noncomputable def mackeySummandQuotientWithTransversal
    (H K : OpenSubgroup G) [H.toSubgroup.FiniteIndex] (x : G)
    (T : (mackeyOpenStabilizer H K x).toSubgroup.RightTransversal)
    [TopRep.JointlyContinuous X] :
    (continuousCrossedHom (TopRep.res H.subtype X) ⧸
        principalCocycles (TopRep.res H.subtype X)) →L[k]
      (continuousCrossedHom (TopRep.res K.subtype X) ⧸
        principalCocycles (TopRep.res K.subtype X)) := by
  let _ := mackeyOpenStabilizerFiniteIndex H K x
  exact (transferQuotient (TopRep.res K.subtype X)
      (mackeyOpenStabilizer H K x) T).comp
    (mackeyConjugateQuotient X H K x)

end CorestrictionTransversal
end ContinuousCohomology
end
end
