@[expose] public section

open List (Vector)

open Function

attribute [local instance] Vector.Perm.isSetoid

namespace Sym

variable {α β : Type*} {n n' m : ℕ} {s : Sym α n} {a b : α}

@[inherit_doc]
infixr:67 " ::ₛ " => cons

/-- `erase s a h` is the sym that subtracts 1 from the
  multiplicity of `a` if `a` is present in the sym. -/
def erase [DecidableEq α] (s : Sym α (n + 1)) (a : α) (h : a ∈ s) : Sym α n :=
  ⟨s.val.erase a, (Multiset.card_erase_of_mem h).trans <| s.property.symm ▸ n.pred_succ⟩

end Sym
end
