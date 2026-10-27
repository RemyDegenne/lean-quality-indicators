public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open

open CFSG.Blueprint (LieModel classicalTags)

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KE CFSG.Timmesfeld CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.ComponentClassification.CatLeafProof

open scoped MatrixGroups Matrix

set_option maxRecDepth 100000

theorem l154td4_exact_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (hp : p = 2) (ht : t ≠ .trialityD4) (h : LieModel X t n p f) : L154ExactModel X := by
  subst hp
  exact Or.inl ⟨t, n, f, h, ht⟩

end CFSG.LocalAnalysis.GLTheoremA.K155X
end
