public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator CFSG.HardMathSupport.Seitz.Proving

section Matrices

variable {L L' : Type} [Field L] [Field L']

theorem mapSL_HSL (f : L →+* L') (t : Lˣ) :
    Matrix.SpecialLinearGroup.map f (HSL t) = HSL (Units.map f.toMonoidHom t) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [HSL]

end Matrices
end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit
end
