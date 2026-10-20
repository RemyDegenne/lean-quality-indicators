public section

variable {α β γ : Type*} (h : α → β) (h' : β → γ)

/-- A function `h : α → β` is Northcott if the sets `{a : α | h a ≤ b}` are all finite. -/
@[mk_iff]
class Northcott [LE β] : Prop where
  finite_le : ∀ b, {a : α | h a ≤ b}.Finite

end
