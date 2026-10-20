set_option warningAsError true

@[expose] public section

universe u v v' w w'

open CategoryTheory

namespace TopRep

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Monoid G]

/-- Raise a morphism of topological representations together with its source
and target carriers and the acting monoid. -/
def uliftMap {X Y : TopRep.{w} k G} (f : X ⟶ Y) :
    (X.ulift : TopRep.{max w w'} k (ULift.{v'} G)) ⟶
      (Y.ulift : TopRep.{max w w'} k (ULift.{v'} G)) :=
  TopRep.ofHom
    { toContinuousLinearMap :=
        (show ULift.{w'} Y ≃L[k] Y from
          ContinuousLinearEquiv.ulift).symm.toContinuousLinearMap.comp
          (f.hom.toContinuousLinearMap.comp
            (show ULift.{w'} X ≃L[k] X from
              ContinuousLinearEquiv.ulift).toContinuousLinearMap)
      isIntertwining' := fun g => by
        ext x
        change f.hom (X.ρ g.down x.down) = Y.ρ g.down (f.hom x.down)
        exact f.hom.isIntertwining g.down x.down }

end TopRep
end
