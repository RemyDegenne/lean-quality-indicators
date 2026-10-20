@[expose] public section

universe u

variable {α : Type u}

section Group

variable [Group α] [LE α]

section Right

variable [MulRightMono α] {a : α}

/-- `x ↦ x / a` as an order isomorphism. -/
@[to_additive (attr := simps!) /-- `x ↦ x - a` as an order isomorphism. -/]
def OrderIso.divRight (a : α) : α ≃o α where
  toEquiv := Equiv.divRight a
  map_rel_iff' {_ _} := div_le_div_iff_right a

end Right
end Group
end
