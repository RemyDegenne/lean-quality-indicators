public section

noncomputable section

open CategoryTheory Topology

universe u

namespace TauCeti

namespace CoveringSpace

variable {X : TopCat.{u}} [PathConnectedSpace X] [LocallyPathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X]

/-- **The classification of covering spaces by fundamental-groupoid actions.** Over a
path-connected, locally path-connected, semilocally simply connected base, monodromy is an
equivalence from covering spaces to functors from the fundamental groupoid to types. -/
def monodromyEquivalence (X : TopCat.{u}) [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] :
    CoveringSpace X ≌ (FundamentalGroupoid X ⥤ Type u) :=
  (monodromyFunctor X).asEquivalence

end CoveringSpace
end TauCeti
end
end
