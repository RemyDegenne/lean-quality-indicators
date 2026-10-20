@[expose] public section

open Function Set Filter Topology

variable {X α α' β γ δ M R : Type*}

section CompactSupport2

section Monoid

variable [TopologicalSpace α] [MulOneClass β]

variable {f f' : α → β}

@[to_additive, simp]
protected lemma HasCompactMulSupport.one {α β : Type*} [TopologicalSpace α] [One β] :
    HasCompactMulSupport (1 : α → β) := by
  simp [HasCompactMulSupport]

end Monoid
end CompactSupport2
end
