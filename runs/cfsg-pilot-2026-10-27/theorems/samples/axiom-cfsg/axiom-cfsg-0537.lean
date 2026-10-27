public section

namespace CFSG.PSL2Table

open Matrix

open scoped MatrixGroups

variable {F : Type} [Field F]

variable [Fintype F]

section Unipotent

variable {F : Type} [Field F]

theorem mk_unip_eq_one_iff (h2 : (2 : F) ≠ 0) (t : F) : mk (unip t) = 1 ↔ t = 0 := by
  rw [← mk_unip_eq_mk_unip_iff h2 t 0, unip_zero, map_one]

end Unipotent
end CFSG.PSL2Table
end
