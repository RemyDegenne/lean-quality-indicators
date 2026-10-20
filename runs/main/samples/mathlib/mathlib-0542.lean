@[expose] public section

variable {α β γ : Type*} {ι : Sort*} {π : α → Type*}

open Equiv.Perm Function

namespace Set

section domRestrict

theorem domRestrict_def (s : Set α) : s.domRestrict (π := π) = fun f x ↦ f x := rfl

end domRestrict
end Set
end
