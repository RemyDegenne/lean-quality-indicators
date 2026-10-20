@[expose] public section

universe u v

variable {α : Type u} {β : Type v}

section OrderTop

variable [PartialOrder α] [OrderTop α] [Preorder β] {a b : α}

@[to_dual]
lemma top_notMem_iff {s : Set α} : ⊤ ∉ s ↔ ∀ x ∈ s, x < ⊤ :=
  ⟨fun h x hx ↦ Ne.lt_top (fun hx' : x = ⊤ ↦ h (hx' ▸ hx)), fun h h₀ ↦ (h ⊤ h₀).false⟩

end OrderTop
end
