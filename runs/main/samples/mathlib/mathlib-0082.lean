public section

open Function OrderDual

universe u v

variable {α : Type u} {β : Type v}

section Logic

section Preorder

variable [Preorder α]

theorem antitone_le {x : α} : Antitone (· ≤ x) := fun _ _ h' h => h'.trans h

end Preorder
end Logic
end
