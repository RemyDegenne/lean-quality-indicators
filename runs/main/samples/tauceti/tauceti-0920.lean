public section

noncomputable section

open CategoryTheory Topology

universe u

namespace TauCeti.CoveringSpace

variable {X : Type u} [TopologicalSpace X] [LocallyPathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X]

@[simp]
theorem monodromyEquivalenceOfLocallyPathConnectedSpace_functor (X : Type u)
    [TopologicalSpace X] [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] :
    (monodromyEquivalenceOfLocallyPathConnectedSpace X).functor =
      monodromyFunctor (TopCat.of X) :=
  (rfl)

end TauCeti.CoveringSpace
end
end
