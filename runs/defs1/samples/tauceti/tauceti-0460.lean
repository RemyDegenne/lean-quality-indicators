public section

noncomputable section

open CategoryTheory Topology

universe u

namespace TauCeti.FiniteCoveringSpace

variable {X : TopCat.{u}} (x₀ : X) [PathConnectedSpace X] [LocallyPathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X]

/-- The functor taking a finite covering space of `X` to the fibre over `x₀`, a finite set with
the monodromy action of `π₁(X, x₀)`. -/
def finiteFiberActionFunctor :
    FiniteCoveringSpace X ⥤ FiniteAction.{u} (FundamentalGroup X x₀) :=
  ObjectProperty.lift _ (forget X ⋙ CoveringSpace.fiberActionFunctor x₀) fun p =>
    (isFiniteAction_iff _).2 (finite_fiber p x₀)

end TauCeti.FiniteCoveringSpace
end
end
