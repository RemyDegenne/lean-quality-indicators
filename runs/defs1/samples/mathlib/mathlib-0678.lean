@[expose] public section

variable {F ι α β γ : Type*} (f : α → β → β) (op : α → α → α)

namespace Multiset

variable [Monoid α] [Monoid β]

/-- Product of a `s : Multiset α` with `[Monoid α]`, given a proof that `*` commutes
on all elements `x ∈ s`. -/
@[to_additive
      /-- Sum of a `s : Multiset α` with `[AddMonoid α]`, given a proof that `+` commutes
      on all elements `x ∈ s`. -/]
def noncommProd (s : Multiset α) (comm : { x | x ∈ s }.Pairwise Commute) : α :=
  s.noncommFold (· * ·) comm 1

end Multiset
end
