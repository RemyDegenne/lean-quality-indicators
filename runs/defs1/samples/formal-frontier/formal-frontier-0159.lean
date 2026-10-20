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

/-- The representative-independent quotient-level summand attached to a
double coset. It computes on canonical representatives. -/
@[expose]
noncomputable def mackeyDoubleCosetSummand
    (H K : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    [TopRep.JointlyContinuous X]
    (q : DoubleCoset.Quotient (H : Set G) K) :
    (continuousCrossedHom (TopRep.res H.subtype X) ⧸
        principalCocycles (TopRep.res H.subtype X)) →L[k]
      (continuousCrossedHom (TopRep.res K.subtype X) ⧸
        principalCocycles (TopRep.res K.subtype X)) :=
  Quotient.lift (fun x => mackeySummandQuotient X H K x) (by
    intro x y hxy
    obtain ⟨h, hh, b, hb, rfl⟩ := DoubleCoset.rel_iff.mp hxy
    exact (mackeySummandQuotient_mul_left_mul_right X H K x
      ⟨h, hh⟩ ⟨b, hb⟩).symm) q

end CorestrictionTransversal
end ContinuousCohomology
end
end
