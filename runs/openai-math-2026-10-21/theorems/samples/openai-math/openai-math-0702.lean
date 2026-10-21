namespace OAI

noncomputable section

open Set Metric Topology BigOperators

open Set Metric Topology

open Set Metric Topology

open Set Metric Topology

namespace GroupRingTopology.Cellular

universe u v w

variable {X : Type u} [TopologicalSpace X] [T2Space X]

variable {C : Set X} [CWComplex C]

lemma characteristic_mem_skeleton {m n : ℕ} (h : m < n)
    (i : RelCWComplex.cell C m) (x : Disk m) :
    characteristic m i x ∈ Skeleton C n := by
  apply skeleton_mono (Nat.succ_le_of_lt h)
  exact CWComplex.closedCell_subset_skeletonLT m i ⟨x.1,x.2,rfl⟩

end GroupRingTopology.Cellular
end
end OAI
