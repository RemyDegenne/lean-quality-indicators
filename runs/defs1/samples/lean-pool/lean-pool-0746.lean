@[expose] public section

variable {α : Type _}

/-- Split a nonempty list into its head and tail. -/
def List.takeHead : ∀ {l : List α}, l ≠ [] → Σ' (h1 : α) (t : List α), l = h1 :: t
  | [], h => absurd rfl h
  | h1 :: t, _ => ⟨h1, t, rfl⟩

end
