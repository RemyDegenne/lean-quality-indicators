public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

open CFSG.LieType.SteinbergBR.BlockPar

open Matrix

open scoped MatrixGroups

variable {F : Type} [Field F]

variable [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
theorem g22_ne_zero {g : GL (Fin 3) F} (h20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (h21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) : (g : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0 := by
  intro h2
  have hdet : (g : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
    rw [← GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  apply hdet
  rw [Matrix.det_fin_three, h2, h20, h21]
  ring

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
end
