public section

open Function

variable {α β G M : Type*}

attribute [local simp] mul_assoc sub_eq_add_neg

section DivisionCommMonoid

variable [DivisionCommMonoid α] (a b c d : α)

attribute [local simp] mul_assoc mul_comm mul_left_comm div_eq_mul_inv

@[to_additive neg_add]
theorem mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by simp

end DivisionCommMonoid
end
