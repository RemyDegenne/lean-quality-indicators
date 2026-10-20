public section

open Function Set Topology

namespace TauCeti

variable {X Y α : Type*} {k : ℕ}

section Topology

variable [TopologicalSpace X] {θ : Fin k → X → α}

theorem isOpen_sectorSet [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]
    (hc : ∀ i, Continuous (θ i)) (j : Fin (k + 1)) : IsOpen (sectorSet θ j) := by
  simp only [sectorSet, ofPred_and, ofPred_forall]
  refine (isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun _ ↦ ?_).inter
    (isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun _ ↦ ?_)
  · exact isOpen_lt ((hc i).comp continuous_fst) continuous_snd
  · exact isOpen_lt continuous_snd ((hc i).comp continuous_fst)

end Topology
end TauCeti
end
