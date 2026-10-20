public section

namespace TauCeti

open scoped BigOperators

universe u v

variable (Q : Type u) [Quiver.{v} Q] [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)] [DecidableEq Q]

@[simp]
theorem vertexPreReflectionList_flatten_replicate (l : List Q) (N : ℕ) :
    vertexPreReflectionList Q (List.replicate N l).flatten = vertexPreReflectionList Q l ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.replicate_succ, List.flatten_cons, vertexPreReflectionList_append, ih, pow_succ]

end TauCeti
end
