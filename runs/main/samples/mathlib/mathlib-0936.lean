@[expose] public section

open scoped Function

variable {ι α β γ : Type*} {π : ι → Type*}

open Set

section LocallyFiniteOrder

variable {s : Set α} [Preorder α] [LocallyFiniteOrder α]

theorem BddAbove.wellFoundedOn_gt : BddAbove s → s.WellFoundedOn (· > ·) :=
  fun h => h.dual.wellFoundedOn_lt

end LocallyFiniteOrder
end
