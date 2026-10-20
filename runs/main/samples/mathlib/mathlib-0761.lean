public section

open Function

open OrderDual (toDual ofDual)

variable {α : Type*}

namespace Set

section Preorder

variable [Preorder α] {a a₁ a₂ b b₁ b₂ c x : α}

@[to_dual] theorem Ioo_subset_Iio_self : Ioo a b ⊆ Iio b := fun _ => And.right

end Preorder
end Set
end
