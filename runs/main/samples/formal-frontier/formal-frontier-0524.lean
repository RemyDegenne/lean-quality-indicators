@[expose] public section

set_option autoImplicit false

set_option relaxedAutoImplicit false

open Set

universe u v w

namespace TopologicalSpace.IrreducibleCloseds

variable {X : Type u} {Y : Type v} {Z : Type w}

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

@[simp]
theorem opensOrderIso_symm_apply (U : Opens (IrreducibleCloseds X)) :
    (opensOrderIso X).symm U =
      ⟨(unit X) ⁻¹' (U : Set _), U.isOpen.preimage (unit X).continuous⟩ :=
  rfl

end TopologicalSpace.IrreducibleCloseds
end
