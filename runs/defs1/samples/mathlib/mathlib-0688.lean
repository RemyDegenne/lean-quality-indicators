@[expose] public section

open Filter Function Set Topology

variable {X Y W Z : Type*}

section

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W] [TopologicalSpace Z]

namespace Topology.IsEmbedding

/-- Homeomorphism given an embedding. -/
@[simps! apply_coe]
noncomputable def toHomeomorph {f : X → Y} (hf : IsEmbedding f) :
    X ≃ₜ Set.range f :=
  Equiv.ofInjective f hf.injective |>.toHomeomorphOfIsInducing <|
    IsInducing.subtypeVal.of_comp_iff.mp hf.toIsInducing

end Topology.IsEmbedding
end
end
