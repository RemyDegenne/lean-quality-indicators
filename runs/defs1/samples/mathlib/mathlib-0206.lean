@[expose] public section

section GroupStructure

section Subtype

/-- The subgroup of continuous maps `α → β`. -/
@[to_additive /-- The `AddSubgroup` of continuous maps `α → β`. -/]
def continuousSubgroup (α : Type*) (β : Type*) [TopologicalSpace α] [TopologicalSpace β] [Group β]
    [IsTopologicalGroup β] : Subgroup (α → β) :=
  { continuousSubmonoid α β with inv_mem' := fun fc => Continuous.inv fc }

end Subtype
end GroupStructure
end
