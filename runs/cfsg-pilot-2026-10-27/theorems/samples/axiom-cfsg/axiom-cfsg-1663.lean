public section

namespace CFSG.GH74.Generic.BProg.B2.GenLocL4Out

open CFSG CFSG.GH74 Subgroup Matrix

open scoped MatrixGroups

section Lift

variable {F : Type} [Field F]

theorem PiP' (P : GL (Fin 4) F) :
    (P : Matrix (Fin 4) (Fin 4) F) * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

end Lift
end CFSG.GH74.Generic.BProg.B2.GenLocL4Out
end
