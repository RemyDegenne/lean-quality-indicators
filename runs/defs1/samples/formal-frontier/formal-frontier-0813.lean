set_option warningAsError true

@[expose] public section

universe v' v u

open CategoryTheory

namespace TopModuleCat

variable (R : Type u) [Ring R] [TopologicalSpace R]

/-- The original topological module is canonically continuously linearly
equivalent to the carrier of its universe lift. -/
def uliftFunctorObjEquiv (X : TopModuleCat.{v} R) :
    X ≃L[R] (uliftFunctor.{v', v} R).obj X :=
  (ContinuousLinearEquiv.ulift (R₁ := R) (M₁ := X)).symm

end TopModuleCat
end
