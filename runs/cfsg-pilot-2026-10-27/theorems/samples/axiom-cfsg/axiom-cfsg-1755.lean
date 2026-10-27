public noncomputable section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

open CFSG.SignalizerFunctorTheorem.NonLocal CFSG.SignalizerFunctorTheorem.NonLocalExc

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open CFSG.SectionRank.TitsOrder CFSG.SectionRank.TitsGen CFSG.LieType.Simplicity

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem root_1100 : IsRoot ReeTag.F4.tag (![1, 1, 0, 0] : F4Vec) := by
  rw [← z1Reflect_0100]
  exact isRoot_z1Reflect (isRoot_single ReeTag.F4.tag (1 : Fin 4))

end CFSG.SignalizerFunctorTheorem.CatalogBridge
end
