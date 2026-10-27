@[expose] public section

open Function

infixr:25 " →. " => PFun

namespace PFun

variable {α β γ δ ε ι : Type*}

/-- Turns a function into a partial function with a prescribed domain. -/
def res (f : α → β) (s : Set α) : α →. β :=
  (PFun.lift f).restrict s.subset_univ

end PFun
end
