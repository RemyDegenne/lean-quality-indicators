@[expose] public section

universe u v

open Equiv Function Fintype Finset

variable {α : Type u} [DecidableEq α] {β : Type v}

namespace Equiv.Perm

/-- When the list `l : List α` contains all nonfixed points of the permutation `f : Perm α`,
  `signAux2 l f` recursively calculates the sign of `f`. -/
def signAux2 : List α → Perm α → ℤˣ
  | [], _ => 1
  | x::l, f => if x = f x then signAux2 l f else -signAux2 l (swap x (f x) * f)

end Equiv.Perm
end
