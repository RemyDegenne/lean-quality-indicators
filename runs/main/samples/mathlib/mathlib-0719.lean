@[expose] public section

noncomputable section

open Set Filter TopologicalSpace Topology

open scoped ENNReal

variable {α : Type*} [TopologicalSpace α]

namespace EReal

theorem _root_.continuous_coe_real_ereal : Continuous ((↑) : ℝ → EReal) :=
  isEmbedding_coe.continuous

end EReal
end
end
