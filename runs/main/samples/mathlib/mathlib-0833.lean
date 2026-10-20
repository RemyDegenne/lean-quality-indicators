public section

open Order

variable {α : Type*}

namespace Set

variable [LinearOrder α] [One α]

section PredSubOrder

variable [Sub α] [PredSubOrder α] {a b : α}

lemma insert_Icc_left_eq_Icc_sub_one (h : a - 1 ≤ b) :
    insert (a - 1) (Icc a b) = Icc (a - 1) b := by
  simpa [← pred_eq_sub_one] using insert_Icc_left_eq_Icc_pred (pred_eq_sub_one a ▸ h)

end PredSubOrder
end Set
end
