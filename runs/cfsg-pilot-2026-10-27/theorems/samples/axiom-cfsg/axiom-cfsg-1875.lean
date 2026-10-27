public section

namespace CFSG.GH74.QTGen4.DSGen4.L34

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.QuasithinUnique.Fin257.L3
  CFSG.Quasithin.H13.F431.L3.P3

section Main

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem wbK_wbX (a : F) : wbK (wbX a) = xP a := by
  unfold wbK xP
  rfl

end Main
end CFSG.GH74.QTGen4.DSGen4.L34
end
