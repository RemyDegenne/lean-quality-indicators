@[expose] public section

namespace Sym2

variable {α}

/-- The infimum of the two elements. -/
def inf [SemilatticeInf α] (x : Sym2 α) : α := Sym2.lift ⟨(· ⊓ ·), inf_comm⟩ x

end Sym2
end
