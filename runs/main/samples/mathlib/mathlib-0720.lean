@[expose] public section

universe u v

open Function Set Filter

open scoped Topology

noncomputable section

variable {ι : Type u} {X : Type v} [TopologicalSpace X]

namespace PartitionOfUnity

variable {s : Set X}

theorem exists_isSubordinate [NormalSpace X] [ParacompactSpace X] (hs : IsClosed s) (U : ι → Set X)
    (ho : ∀ i, IsOpen (U i)) (hU : s ⊆ ⋃ i, U i) :
    ∃ f : PartitionOfUnity ι X s, f.IsSubordinate U :=
  let ⟨f, hf⟩ := BumpCovering.exists_isSubordinate hs U ho hU
  ⟨f.toPartitionOfUnity, hf.toPartitionOfUnity⟩

end PartitionOfUnity
end
end
