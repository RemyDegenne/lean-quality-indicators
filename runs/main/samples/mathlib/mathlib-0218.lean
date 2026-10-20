@[expose] public section

universe v

open List Nat

variable {α : Type*} {β : Type v}

namespace Multiset

section Erase

variable [DecidableEq α] {s t : Multiset α} {a b : α}

@[simp]
theorem erase_cons_tail {a b : α} (s : Multiset α) (h : b ≠ a) :
    (b ::ₘ s).erase a = b ::ₘ s.erase a :=
  Quot.inductionOn s fun _ => congr_arg _ <| List.erase_cons_tail (not_beq_of_ne h)

end Erase
end Multiset
end
