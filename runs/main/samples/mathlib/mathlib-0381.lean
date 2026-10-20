@[expose] public section

universe v

open List Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

section sub

variable [DecidableEq α] {s t u : Multiset α} {a : α}

@[simp] lemma inf_eq_inter (s t : Multiset α) : s ⊓ t = s ∩ t := rfl

end sub
end Multiset
end
