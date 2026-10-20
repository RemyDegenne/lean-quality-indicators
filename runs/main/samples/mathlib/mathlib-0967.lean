@[expose] public section

namespace OrderMonoidHom

variable (α β : Type*) [Monoid α] [PartialOrder α] [Monoid β] [Preorder β]

@[to_additive]
theorem inlₗ_mul_inrₗ_eq_toLex (m : α) (n : β) : inlₗ α β m * inrₗ α β n = toLex (m, n) := by
  simp [← toLex_mul]

end OrderMonoidHom
end
