public section

open Set

open MeasureTheory

open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]

theorem IsNullSet.mono {I : ModelWithCorners ℝ E H} [MeasurableSpace E] [hE : BorelSpace E]
    {s t : Set M} (ht : IsNullSet I t) (hst : s ⊆ t) : IsNullSet I s := by
  rw [isNullSet_iff] at ht ⊢
  intro x μ hμ
  apply measure_mono_null _ (ht x μ)
  exact image_mono (inter_subset_inter_left _ hst)

end TauCeti
end
