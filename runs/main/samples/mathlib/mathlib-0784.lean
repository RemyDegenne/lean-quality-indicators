public section

open Function Set

namespace Fin

variable {m n : ℕ}

@[simp]
theorem image_succ_Ioo (i j : Fin n) : succ '' Ioo i j = Ioo i.succ j.succ := image_addNat_Ioo ..

end Fin
end
