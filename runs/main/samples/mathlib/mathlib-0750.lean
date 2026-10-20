@[expose] public section

universe u v

open Cardinal

namespace ZFSet

variable {x y : ZFSet.{u}}

theorem card_insert (h : x ∉ y) : card (insert x y) = card y + 1 := by
  rw [← lift_inj.{u, u + 1}]
  simpa [← cardinalMk_coe_sort] using! mk_insert (SetLike.mem_coe.not.2 h)

end ZFSet
end
