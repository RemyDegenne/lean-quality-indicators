public section

open Pointwise

open scoped Interval

variable {α : Type*}

namespace Set

section OrderedCommGroup

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

@[to_additive (attr := simp)]
theorem image_div_const_Ioc : (fun x => x / a) '' Ioc b c = Ioc (b / a) (c / a) := by
  simp [div_eq_mul_inv]

end OrderedCommGroup
end Set
end
