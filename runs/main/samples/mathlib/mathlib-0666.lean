@[expose] public section

open Equiv Equiv.Perm List

variable {α : Type*}

namespace Equiv.Perm

section Fintype

variable [Fintype α] [DecidableEq α] (p : Equiv.Perm α) (x : α)

variable {p} {x}

theorem exists_toCycle_toList (f : Perm α) (hf : IsCycle f) : ∃ x, toCycle f hf = toList f x :=
  Exists.casesOn hf (fun x h => ⟨x, Perm.toCycle_eq_toList f hf x h.1⟩)

end Fintype
end Equiv.Perm
end
