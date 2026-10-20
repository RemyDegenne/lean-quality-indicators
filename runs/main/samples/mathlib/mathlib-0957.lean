public section

open Function

open Nat hiding one_pos

namespace List

universe u v w

variable {ι : Type*} {α : Type u} {β : Type v} {γ : Type w} {l l₁ l₂ : List α}

theorem reverse_cons' (a : α) (l : List α) : reverse (a :: l) = concat (reverse l) a := by
  simp only [reverse_cons, concat_eq_append]

end List
end
