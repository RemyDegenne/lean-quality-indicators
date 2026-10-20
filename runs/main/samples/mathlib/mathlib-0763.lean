public section

open Filter

open scoped Topology

variable {L X : Type*} [TopologicalSpace L] [TopologicalSpace X]

namespace Filter.Tendsto

open Finset

variable {ι α : Type*} {s : Finset ι} {f : ι → α → L} {l : Filter α} {g : ι → L}

lemma finset_sup_nhds [SemilatticeSup L] [OrderBot L] [ContinuousSup L]
    (hs : ∀ i ∈ s, Tendsto (f i) l (𝓝 (g i))) : Tendsto (s.sup f) l (𝓝 (s.sup g)) := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simpa using! tendsto_const_nhds
  · simp only [← sup'_eq_sup hne]
    exact finset_sup'_nhds hne hs

end Filter.Tendsto
end
