@[expose] public section

noncomputable section

open Filter Set

open scoped SetRel Uniformity Topology

universe u v w

open CauchyFilter Set

namespace UniformSpace

variable (α : Type*) [UniformSpace α]

variable {β : Type*} [UniformSpace β]

variable {γ : Type*} [UniformSpace γ]

namespace Completion

attribute [local instance]
  AbstractCompletion.uniformStruct AbstractCompletion.complete AbstractCompletion.separation

variable {α}

open TopologicalSpace

theorem denseRange_coe₂ :
    DenseRange fun x : α × β => ((x.1 : Completion α), (x.2 : Completion β)) :=
  denseRange_coe.prodMap denseRange_coe

end Completion
end UniformSpace
end
end
