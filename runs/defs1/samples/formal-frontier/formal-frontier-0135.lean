set_option autoImplicit false

public section

open CategoryTheory

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace ContinuousCohomology

variable (X : TopRep.{max v w} k G)

variable {A B C : TopRep.{max v w} k G}

/-- The first continuous cohomology object, identified with the quotient of
continuous crossed homomorphisms by principal cocycles. The canonical inverse
computes in the corestriction comparison. -/
@[expose]
noncomputable def homologyQuotientIso [TopRep.JointlyContinuous X] :
    continuousCohomology 1 X ≅
      TopModuleCat.of k (continuousCrossedHom X ⧸ principalCocycles X) :=
  Limits.CokernelCofork.mapIsoOfIsColimit
    ((TopRep.homogeneousCochains X).homologyIsCokernel 0 1 (by simp))
    (TopModuleCat.isColimitCoker (TopModuleCat.ofHom (principalToCrossedL X)))
    (boundaryArrowIso X)

end ContinuousCohomology
end
