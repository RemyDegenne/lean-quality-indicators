@[expose] public section

open Finset Function

variable {α β : Type*}

namespace Finset

section Preorder

variable [Preorder α]

section LocallyFiniteOrder

variable [LocallyFiniteOrder α] {a b x : α}

@[to_dual (reorder := a b) (attr := simp, norm_cast)]
theorem coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b :=
  Set.ext fun _ => mem_Ico

end LocallyFiniteOrder
end Preorder
end Finset
end
