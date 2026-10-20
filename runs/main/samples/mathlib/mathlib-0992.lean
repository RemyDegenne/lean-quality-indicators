@[expose] public section

open Set OrderDual

variable {ι α β : Type*}

variable {P Q : α → Prop} {a x y : α}

section LinearOrder

variable [LinearOrder α] {i j : ι} {Q : ι → Prop} {f : ι → α}

@[to_dual]
theorem Minimal.le (h : Minimal P x) (hy : P y) : x ≤ y :=
  le_of_not_gt (h.not_lt hy)

end LinearOrder
end
