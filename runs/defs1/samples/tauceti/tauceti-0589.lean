public section

noncomputable section

open CategoryTheory Topology

universe u

namespace TauCeti.FiniteCoveringSpace

variable {X : TopCat.{u}} (x₀ : X) [PathConnectedSpace X] [LocallyPathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X]

/-- The fibre-action functor of finite covers, followed by the inclusion of finite `π₁(X, x₀)`-sets
into all of them, is the fibre-action functor of covers restricted to finite ones. -/
def finiteFiberActionFunctorCompForgetIso :
    finiteFiberActionFunctor x₀ ⋙ FiniteAction.forget (FundamentalGroup X x₀) ≅
      forget X ⋙ CoveringSpace.fiberActionFunctor x₀ :=
  ObjectProperty.liftCompιIso _ _ _

end TauCeti.FiniteCoveringSpace
end
end
