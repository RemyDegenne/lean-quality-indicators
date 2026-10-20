@[expose] public section

open Function

variable {ι α β : Type*} {π : ι → Type*}

@[inherit_doc] infixl:80 " ⁻¹'o " => Order.Preimage

section LinearOrder

variable [LinearOrder α] [DenselyOrdered α] {a₁ a₂ : α}

@[to_dual eq_of_le_of_forall_gt_imp_ge_of_dense]
lemma eq_of_le_of_forall_lt_imp_le_of_dense (h₁ : a₂ ≤ a₁) (h₂ : ∀ a, a₂ < a → a₁ ≤ a) : a₁ = a₂ :=
  le_antisymm (le_of_forall_gt_imp_ge_of_dense h₂) h₁

end LinearOrder
end
