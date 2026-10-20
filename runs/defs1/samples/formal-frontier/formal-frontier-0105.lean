@[expose] public section

set_option autoImplicit false

set_option relaxedAutoImplicit false

open Set

universe u v w

namespace TopologicalSpace.IrreducibleCloseds

variable {X : Type u} {Y : Type v} {Z : Type w}

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A sober space is homeomorphic to its soberification via the unit. -/
noncomputable def unitHomeomorph (X : Type u) [TopologicalSpace X]
    [QuasiSober X] [T0Space X] : X ≃ₜ IrreducibleCloseds X := by
  letI : PartialOrder X := specializationOrder X
  exact {
    toEquiv := (irreducibleSetEquivPoints (α := X)).symm.toEquiv
    continuous_toFun := (unit X).continuous
    continuous_invFun := by
      rw [continuous_def]
      intro S hS
      convert (openSet ⟨S, hS⟩).isOpen using 1
      ext F
      change F.isIrreducible.genericPoint ∈ S ↔ ((F : Set X) ∩ S).Nonempty
      exact (F.isIrreducible.isGenericPoint_genericPoint F.isClosed).mem_open_set_iff hS }

end TopologicalSpace.IrreducibleCloseds
end
