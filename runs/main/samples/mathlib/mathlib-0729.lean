@[expose] public section

open Filter Function Set Uniformity Topology

open scoped SetRel

theorem Embedding.to_isUniformEmbedding {α β} [TopologicalSpace α] [u : UniformSpace β] (f : α → β)
    (h : IsEmbedding f) : @IsUniformEmbedding α β (h.comapUniformSpace f) u f :=
  let _ := h.comapUniformSpace f
  { comap_uniformity := rfl
    injective := h.injective }

end
