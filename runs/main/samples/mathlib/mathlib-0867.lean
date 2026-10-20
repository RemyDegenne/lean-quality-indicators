@[expose] public section

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

section

variable (p : α → Prop) [DecidablePred p]

variable {p}

variable (p)

@[simp]
theorem filterMap_add (f : α → Option β) (s t : Multiset α) :
    filterMap f (s + t) = filterMap f s + filterMap f t :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ => congr(ofList $filterMap_append)

end
end Multiset
end
