@[expose] public section

open Set Filter Topology TopologicalSpace Function

universe u v

variable {X : Type u} {Y : Type v} {ι : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X} {f : X → Y}

section Compact

theorem Topology.IsClosedEmbedding.isCompact_preimage (hf : IsClosedEmbedding f)
    {K : Set Y} (hK : IsCompact K) : IsCompact (f ⁻¹' K) :=
  hf.isInducing.isCompact_preimage (hf.isClosed_range) hK

end Compact
end
