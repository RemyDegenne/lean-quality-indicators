public section

open Pointwise

open scoped Interval

variable {α : Type*}

namespace Set

section OrderedCommGroup

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

@[to_additive]
theorem image_inv_Ico : Inv.inv '' Ico a b = Ioc (b⁻¹) (a⁻¹) := by simp

end OrderedCommGroup
end Set
end
