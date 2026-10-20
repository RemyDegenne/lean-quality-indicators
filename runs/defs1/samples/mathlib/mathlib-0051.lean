@[expose] public section

noncomputable section

open Topology TopologicalSpace Set Filter Function

universe u v u' v'

variable {X : Type u} {Y : Type v} {W Z ε ζ : Type*}

section Prod

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
  [TopologicalSpace ε] [TopologicalSpace ζ]

namespace Homeomorph

variable {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']

variable (W X Y Z)

/-- `X × {*}` is homeomorphic to `X`. -/
@[simps! -fullyApplied apply]
def prodPUnit : X × PUnit ≃ₜ X where
  toEquiv := Equiv.prodPUnit X

end Homeomorph
end Prod
end
end
