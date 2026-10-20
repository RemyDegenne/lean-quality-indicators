public section

namespace TauCeti

universe u v

section Kernel

variable (G : Type u) [Group G] (M : Type v) [MulAction G M]

variable [TopologicalSpace G] [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

@[simp]
theorem openActionKernel_toSubgroup [Finite M] :
    (openActionKernel G M).toSubgroup = (MulAction.toPermHom G M).ker :=
  (rfl)

end Kernel
end TauCeti
end
