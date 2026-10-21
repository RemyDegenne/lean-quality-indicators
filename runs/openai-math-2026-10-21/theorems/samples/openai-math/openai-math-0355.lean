namespace OAI

noncomputable section

open MeasureTheory Set

open scoped Topology Classical Function

namespace InvariantIsing

lemma spectralPartitionIndex_eq_iff {ι : Type*} (S : ι → Set ℝ)
    (hcover : ∀ x, ∃ i, x∈S i) (hdis : Pairwise (Disjoint on S)) (x : ℝ) (i : ι) :
    spectralPartitionIndex S hcover x=i ↔ x∈S i := by
  constructor
  · intro h
    rw [← h]
    exact spectralPartitionIndex_mem S hcover x
  · intro hx
    by_contra hne
    exact (Set.disjoint_left.mp (hdis hne)) (spectralPartitionIndex_mem S hcover x) hx

end InvariantIsing
end
end OAI
