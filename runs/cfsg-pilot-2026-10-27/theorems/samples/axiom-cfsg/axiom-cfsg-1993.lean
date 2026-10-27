public section

namespace CFSG.GH74.QTGen4.DSGen4.Lin2A

open Matrix

section Natural

variable (F : Type*) [Field F] [Algebra (ZMod 2) F]

theorem natLin_apply (g : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) :
    natLin F g v = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ v :=
  rfl

end Natural
end CFSG.GH74.QTGen4.DSGen4.Lin2A
end
