@[expose] public section

universe v

open List Subtype Nat

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

@[inherit_doc Multiset.cons]
infixr:67 " ::ₘ " => Multiset.cons

@[elab_as_elim]
protected theorem induction_on {p : Multiset α → Prop} (s : Multiset α) (empty : p 0)
    (cons : ∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) : p s :=
  Multiset.induction empty cons s

end Multiset
end
