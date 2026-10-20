@[expose] public section

set_option autoImplicit false

set_option relaxedAutoImplicit false

open Set

universe u v w

namespace TopologicalSpace.IrreducibleCloseds

variable {X : Type u} {Y : Type v} {Z : Type w}

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem unit_isEmbedding_iff_t0 (X : Type u) [TopologicalSpace X] :
    Topology.IsEmbedding (unit X) ↔ T0Space X := by
  rw [Topology.isEmbedding_iff, unit_injective_iff_t0]
  simp only [unit_isInducing, true_and]

end TopologicalSpace.IrreducibleCloseds
end
