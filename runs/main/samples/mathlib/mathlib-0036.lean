@[expose] public section

open Function

open OrderDual (toDual ofDual)

variable {α β : Type*}

namespace Set

section Lattice

variable [Lattice α] [Lattice β] {a a₁ a₂ b b₁ b₂ x : α}

scoped[Interval] notation "[[" a ", " b "]]" => Set.uIcc a b

open scoped Interval

@[simp] lemma left_mem_uIcc : a ∈ [[a, b]] := ⟨inf_le_left, le_sup_left⟩

end Lattice
end Set
end
