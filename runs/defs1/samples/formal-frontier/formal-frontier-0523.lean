@[expose] public section

set_option autoImplicit false

set_option relaxedAutoImplicit false

open Set

universe u v w

namespace TopologicalSpace.IrreducibleCloseds

variable {X : Type u} {Y : Type v} {Z : Type w}

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The open set of irreducible closed subsets meeting `U`. -/
def openSet (U : Opens X) : Opens (IrreducibleCloseds X) :=
  ⟨{F : IrreducibleCloseds X | ((F : Set X) ∩ (U : Set X)).Nonempty}, ⟨U, rfl⟩⟩

end TopologicalSpace.IrreducibleCloseds
end
