@[expose] public section

open Function Multiset Sum

namespace Finset

variable {α β γ : Type*} (s : Finset α) (t : Finset β)

variable {s t} {s₁ s₂ : Finset α} {t₁ t₂ : Finset β} {a : α} {b : β} {x : α ⊕ β}

/--
Given a finset of elements `α ⊕ β`, extract all the elements of the form `α`. This
forms a quasi-inverse to `disjSum`, in that it recovers its left input.

See also `List.partitionMap`.
-/
def toLeft (u : Finset (α ⊕ β)) : Finset α :=
  u.filterMap (Sum.elim some fun _ => none) (by clear x; aesop)

end Finset
end
