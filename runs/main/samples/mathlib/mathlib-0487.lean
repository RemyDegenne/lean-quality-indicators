@[expose] public section

open Function MulOpposite

open scoped Pointwise

variable {F α β : Type*}

namespace Finset

section One

variable [One α] {s : Finset α} {a : α}

scoped[Pointwise] attribute [instance] Finset.one Finset.zero

@[to_additive (attr := simp, norm_cast)]
lemma coe_eq_one : (s : Set α) = 1 ↔ s = 1 := coe_eq_singleton

end One
end Finset
end
