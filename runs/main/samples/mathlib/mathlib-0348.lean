public section

open Filter MeasureTheory Set TopologicalSpace

open scoped Topology

variable {ι X E : Type*} [MeasurableSpace X] [TopologicalSpace E] [Countable ι] {l : Filter ι}
  [l.IsCountablyGenerated] {f : ι → X → E}

namespace MeasureTheory

variable {X E ι : Type*} [MeasurableSpace X] [CommMonoid E] [TopologicalSpace E]

section

variable [PseudoMetrizableSpace E] [ContinuousMul E]
  {L : SummationFilter ι} [L.NeBot] [L.filter.IsCountablyGenerated]

@[to_additive (attr := fun_prop)
]
theorem StronglyMeasurable.tprod' {f : ι → X → E} (h : ∀ i : ι, StronglyMeasurable (f i)) :
    StronglyMeasurable (∏'[L] i : ι, f i) := by
  rw [tprod_def, finprod_def']
  split_ifs with hm
  any_goals exact stronglyMeasurable_one
  · refine Finset.stronglyMeasurable_prod _ (fun _ _ ↦ ?_)
    rw [Set.mulIndicator]
    split_ifs
    · fun_prop
    · exact stronglyMeasurable_one
  · exact stronglyMeasurable_of_tendsto L.filter (by fun_prop) hm.choose_spec

end
end MeasureTheory
end
