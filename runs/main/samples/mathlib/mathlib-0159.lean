@[expose] public section

universe v

open List Subtype Nat

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

@[inherit_doc Multiset.cons]
infixr:67 " ::ₘ " => Multiset.cons

@[simp]
theorem mem_singleton {a b : α} : b ∈ ({a} : Multiset α) ↔ b = a := by
  simp only [← cons_zero, mem_cons, iff_self, or_false, notMem_zero]

end Multiset
end
