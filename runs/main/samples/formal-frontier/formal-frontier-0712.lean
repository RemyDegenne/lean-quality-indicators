public section

open Order Set TopologicalSpace Topology

open TopologicalSpace.IrreducibleCloseds

variable {X : Type*} [TopologicalSpace X]

theorem Topology.IsQuotientMap.topologicalKrullDim_le_zero_of_isOpen_preimage_closedPoint
    {Y : Type*} [TopologicalSpace Y] {f : X → Y} [JacobsonSpace Y]
    (hf : IsQuotientMap f)
    (h : ∀ y ∈ closedPoints Y, IsOpen (f ⁻¹' ({y} : Set Y))) :
    topologicalKrullDim Y ≤ 0 := by
  let _ : DiscreteTopology Y :=
    JacobsonSpace.discreteTopology_of_isOpen_singleton_closedPoint fun y hy ↦ by
      rw [← hf.isOpen_preimage]
      exact h y hy
  exact topologicalKrullDim_zero_of_discreteTopology Y

end
