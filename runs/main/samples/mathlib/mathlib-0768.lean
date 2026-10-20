public section

open ENNReal

open scoped Topology

open Set Function Filter

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace γ] {f : α → β} {s t : Set α}
  {x : α} {y z : β}

section

variable {α : Type*} [TopologicalSpace α]

variable {β : Type*}

variable {γ : Type*} [TopologicalSpace γ]

variable {f : α → β} {s : Set α} {a : α}

variable [PartialOrder β] [CommGroup β] [IsOrderedMonoid β]

@[to_additive (attr := simp)]
theorem lowerSemiContinuous_inv_iff :
    LowerSemicontinuous f⁻¹ ↔ UpperSemicontinuous f := by
  simp [← upperSemicontinuousOn_univ_iff, ← lowerSemicontinuousOn_univ_iff]

end
end
