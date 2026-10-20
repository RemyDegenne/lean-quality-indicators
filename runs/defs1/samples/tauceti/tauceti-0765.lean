public section

noncomputable section

open CategoryTheory Topology

universe u

namespace TauCeti.FiniteCoveringSpace

variable {X : TopCat.{u}} (x₀ : X) [PathConnectedSpace X] [LocallyPathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X]

/-- The fibre of a finite covering space over `x₀`, as a functor to finite sets. -/
-- Expose the body so actions transported through the classification equivalence act
-- definitionally on the values of this functor.
@[expose] def fiberFunctor : FiniteCoveringSpace X ⥤ FintypeCat.{u} :=
  (fiberActionFintypeCatEquivalence x₀).functor ⋙ Action.forget FintypeCat _

end TauCeti.FiniteCoveringSpace
end
end
