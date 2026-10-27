@[expose] public section

noncomputable section

open Topology TopologicalSpace Set Filter Function

universe u v u' v'

variable {X : Type u} {Y : Type v} {W Z ε ζ : Type*}

section Sum

open Sum

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W] [TopologicalSpace Z]

namespace Homeomorph

variable {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']

variable (W X Y Z)

set_option backward.defeqAttrib.useBackward true in
/-- Four-way commutativity of the disjoint union. The name matches `add_add_add_comm`. -/
def sumSumSumComm : (X ⊕ Y) ⊕ W ⊕ Z ≃ₜ (X ⊕ W) ⊕ Y ⊕ Z where
  toEquiv := Equiv.sumSumSumComm X Y W Z

end Homeomorph
end Sum
end
end
