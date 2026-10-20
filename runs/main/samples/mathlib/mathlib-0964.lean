@[expose] public section

universe u

variable {x y z w : ZFSet.{u}}

open Set

namespace ZFSet

protected theorem IsTransitive.union (hx : x.IsTransitive) (hy : y.IsTransitive) :
    (x ∪ y).IsTransitive := by
  rw [← sUnion_pair]
  apply IsTransitive.sUnion'
  intro
  rw [mem_pair]
  rintro (rfl | rfl)
  assumption'

end ZFSet
end
