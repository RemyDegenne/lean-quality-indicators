set_option autoImplicit false

public section

open CategoryTheory

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace ContinuousCohomology

variable (X : TopRep.{max v w} k G)

variable {A B C : TopRep.{max v w} k G}

/-- A coefficient morphism sends continuous crossed homomorphisms forward.
Its application to a cocycle computes pointwise in external clients. -/
@[expose]
def crossedMap (q : A ⟶ B) :
    continuousCrossedHom A →L[k] continuousCrossedHom B :=
  ((ContinuousLinearMap.compLeftContinuous k G q.hom.toContinuousLinearMap).comp
      (Submodule.subtypeL (continuousCrossedHom A))).codRestrict
    (continuousCrossedHom B) fun f g h => by
      change q (f.1 (g * h)) = B.ρ g (q (f.1 h)) + q (f.1 g)
      rw [f.2, map_add, TopRep.hom_comm_apply]

end ContinuousCohomology
end
