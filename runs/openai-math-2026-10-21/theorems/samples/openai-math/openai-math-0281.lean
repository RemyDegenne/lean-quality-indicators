namespace OAI

noncomputable section

open Set MeasureTheory Metric Filter Topology

open scoped NNReal RealInnerProductSpace Pointwise

namespace PettyProjection

variable {n : ℕ}

lemma linearEquiv_nhds (T : Space n ≃L[ℝ] Space n) {K : Set (Space n)}
    (h0 : K∈𝓝 (0:Space n)) : T '' K∈𝓝 (0:Space n) := by
  have hh := T.toHomeomorph.isOpenMap.image_mem_nhds h0
  change T '' K∈𝓝 (T 0) at hh
  simpa only [map_zero] using hh

end PettyProjection
end
end OAI
