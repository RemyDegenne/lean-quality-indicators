public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.RF4 CFSG.Quasithin.G2U CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.SEITZ3 CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.RankThree.Classical

section Torus

variable {L : Type} [Field L]

theorem rootChar_tuple (u w : Lˣ) (m n : ℤ) :
    rootChar (tup u w) (vec m n) = u ^ m * w ^ n := by
  rw [rootChar]
  refine (Fin.prod_univ_two _).trans ?_
  rfl

end Torus
end CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding
end
