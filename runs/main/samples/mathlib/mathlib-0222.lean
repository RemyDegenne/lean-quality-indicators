@[expose] public section

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

open Nat

namespace List

@[simp]
theorem mem_sublists' {s t : List α} : s ∈ sublists' t ↔ s <+ t := by
  induction t generalizing s with
  | nil =>
    simp only [sublists'_nil, mem_singleton]
    exact ⟨fun h => by rw [h], eq_nil_of_sublist_nil⟩
  | cons a t IH => ?_
  simp only [sublists'_cons, mem_append, IH, mem_map]
  constructor <;> intro h
  · rcases h with (h | ⟨s, h, rfl⟩)
    · exact sublist_cons_of_sublist _ h
    · exact h.cons_cons _
  · obtain - | ⟨-, h⟩ | ⟨-, h⟩ := h
    · exact Or.inl h
    · exact Or.inr ⟨_, h, rfl⟩

end List
end
