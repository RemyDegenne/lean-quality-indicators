@[expose] public section

open Function OrderDual

variable {ι α β : Type*} {π : ι → Type*}

scoped[symmDiff] infixl:100 " ∆ " => symmDiff

scoped[symmDiff] infixl:100 " ⇔ " => bihimp

open scoped symmDiff

section BooleanAlgebra

variable [BooleanAlgebra α] (a b c d : α)

variable {a b c}

theorem Codisjoint.bihimp_inf_bihimp_le_right (h : Codisjoint b c) : a ⇔ b ⊓ a ⇔ c ≤ a :=
  h.dual.le_symmDiff_sup_symmDiff_right

end BooleanAlgebra
end
