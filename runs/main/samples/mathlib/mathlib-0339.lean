@[expose] public section

namespace List

variable {α : Type*} [DecidableEq α]

variable (l : List α) (x : α)

theorem next_cons_concat (y : α) (hy : x ≠ y) (hx : x ∉ l)
    (h : x ∈ y :: l ++ [x] := mem_append_right _ (mem_singleton_self x)) :
    next (y :: l ++ [x]) x h = y := by
  rw [next, nextOr_concat]
  · simp
  · simp [hy, hx]

end List
end
