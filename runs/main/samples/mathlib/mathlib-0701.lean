@[expose] public section

namespace List

universe u v

variable {α : Type u} {β : Type v} (l : List α) (x : α) (xs : List α) (n : ℕ)

section getI

variable [Inhabited α]

theorem getI_append (l l' : List α) (n : ℕ) (h : n < l.length) :
    (l ++ l').getI n = l.getI n := getD_append _ _ _ _ h

end getI
end List
end
