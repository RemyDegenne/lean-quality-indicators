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

/-- Conjugation and restriction descend to crossed homomorphisms modulo
principal crossed homomorphisms. Its lift computes on representatives. -/
@[expose]
def mackeyConjugateQuotient (H K : OpenSubgroup G) (x : G)
    [TopRep.JointlyContinuous X] :
    (continuousCrossedHom (TopRep.res H.subtype X) ⧸
        principalCocycles (TopRep.res H.subtype X)) →L[k]
      (continuousCrossedHom
          (TopRep.res (mackeyOpenStabilizer H K x).subtype
            (TopRep.res K.subtype X)) ⧸
        principalCocycles
          (TopRep.res (mackeyOpenStabilizer H K x).subtype
            (TopRep.res K.subtype X))) :=
  (principalCocycles (TopRep.res H.subtype X)).liftQL
    ((principalCocycles
      (TopRep.res (mackeyOpenStabilizer H K x).subtype
        (TopRep.res K.subtype X))).mkQL.comp
      (mackeyConjugateCrossed X H K x)) <| by
      intro f hf
      rw [LinearMap.mem_ker]
      change (principalCocycles
        (TopRep.res (mackeyOpenStabilizer H K x).subtype
          (TopRep.res K.subtype X))).mkQL
          (mackeyConjugateCrossed X H K x f) = 0
      change f ∈ LinearMap.range
        (principalToCrossed (TopRep.res H.subtype X)) at hf
      rcases hf with ⟨c, rfl⟩
      rw [mackeyConjugateCrossed_principal]
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨X.ρ x⁻¹ c, rfl⟩

end CorestrictionTransversal
end ContinuousCohomology
end
end
