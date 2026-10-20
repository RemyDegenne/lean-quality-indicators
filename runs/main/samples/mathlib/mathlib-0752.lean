public section

open Finset Function

namespace Fin

variable (n : ℕ)

variable {n}

variable {m : ℕ} (a b : Fin n)

@[simp]
theorem attachFin_Ico :
    attachFin (Ico a b) (fun _x hx ↦ (mem_Ico.mp hx).2.trans b.2) = Ico a b :=
  rfl

end Fin
end
