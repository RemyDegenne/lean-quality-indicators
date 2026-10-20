@[expose] public section

open Function Set Filter Topology TopologicalSpace

universe u v

variable {X : Type*} {Y : Type*} [TopologicalSpace X]

section Separation

/-- Specialization forms a partial order on a t0 topological space. -/
@[instance_reducible]
def specializationOrder (X) [TopologicalSpace X] [T0Space X] : PartialOrder X :=
  { specializationPreorder X, PartialOrder.lift (OrderDual.toDual ∘ 𝓝) nhds_injective with }

end Separation
end
