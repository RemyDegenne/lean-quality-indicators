@[expose] public section

open Filter Set TopologicalSpace Function

open Filter Pointwise

open scoped Topology

universe u

/-- A `GroupFilterBasis` on a group is a `FilterBasis` satisfying some additional axioms.
  Example : if `G` is a topological group then the neighbourhoods of the identity are a
  `GroupFilterBasis`. Conversely given a `GroupFilterBasis` one can define a topology
  compatible with the group structure on `G`. -/
class GroupFilterBasis (G : Type u) [Group G] extends FilterBasis G where
  one' : ∀ {U}, U ∈ sets → (1 : G) ∈ U
  mul' : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V * V ⊆ U
  inv' : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (fun x ↦ x⁻¹) ⁻¹' U
  conj' : ∀ x₀, ∀ {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (fun x ↦ x₀ * x * x₀⁻¹) ⁻¹' U

end
