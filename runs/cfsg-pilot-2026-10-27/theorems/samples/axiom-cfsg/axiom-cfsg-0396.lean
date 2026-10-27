public section

namespace CFSG.Quasithin.H13.KG4413

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.Quasithin.SteinbergBS CFSG.QuasithinUnique

open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

open scoped MatrixGroups

section Cycle

variable {F : Type} [Field F]

variable [CharP F 2]

theorem w0L3_mul_cyc3L3_inv_mul_w0L3 : w0L3 F * (cyc3L3 F)⁻¹ * w0L3 F = cyc3L3 F := by
  rw [cyc3L3_inv, w0L3, cyc3L3, ← map_mul, ← map_mul, wJ_mul_cyc3iSL_mul_wJ]

end Cycle
end CFSG.Quasithin.H13.KG4413
end
