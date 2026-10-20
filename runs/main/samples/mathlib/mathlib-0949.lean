@[expose] public section

universe v

open List Subtype Nat

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

@[inherit_doc Multiset.cons]
infixr:67 " ::ₘ " => Multiset.cons

section Mem

theorem empty_or_exists_mem (s : Multiset α) : s = 0 ∨ ∃ a, a ∈ s :=
  or_iff_not_imp_left.mpr Multiset.exists_mem_of_ne_zero

end Mem
end Multiset
end
