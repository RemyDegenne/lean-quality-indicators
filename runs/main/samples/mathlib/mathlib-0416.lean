public section

variable {α : Type*} {a b : α}

section SemilatticeSup

variable [SemilatticeSup α] [One α] [IsBotOneClass α]

@[to_additive]
theorem one_sup (a : α) : 1 ⊔ a = a := by simp

end SemilatticeSup
end
