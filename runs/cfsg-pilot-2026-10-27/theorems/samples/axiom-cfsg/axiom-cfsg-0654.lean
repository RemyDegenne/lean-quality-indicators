public section

namespace CFSG.PSL2Table

open Matrix

open scoped MatrixGroups

variable {F : Type} [Field F]

theorem splitWeyl_mul_self : splitWeyl F * splitWeyl F = 1 := by
  rw [splitWeyl, ← map_mul, weyl_sq, mk_neg, map_one]

end CFSG.PSL2Table
end
