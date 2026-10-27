public section

namespace CFSG.GH74.Generic.BProg.B2.GenLocL4Gen4

open CFSG CFSG.GH74 Subgroup Matrix

section Core

variable {F : Type*} [Field F]

variable (i : F) (hi : i * i = -1)

theorem relX_ZR : ((gZR i hi : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (gX : GL (Fin 2) F) =
    ((-1 : Fˣ) : F) • ((gX : GL (Fin 2) F) * (gZR i hi : GL (Fin 2) F)) := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [gZR, gX, Matrix.mul_apply, Fin.sum_univ_two]

end Core
end CFSG.GH74.Generic.BProg.B2.GenLocL4Gen4
end
