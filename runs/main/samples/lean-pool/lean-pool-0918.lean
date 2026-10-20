@[expose] public section

namespace LeanPool.DemazureProduct

namespace Valley

variable (v : Valley)

lemma min_mem : ∃ a ∈ {n | v.f n ≤ v.f 0}, v.f a = v.min := by
  simpa [min, Finset.mem_image] using
    Finset.min'_mem (Finset.image v.f (v.floor (v.f 0))) (v.floor_image_nonempty 0)

end Valley
end LeanPool.DemazureProduct
end
