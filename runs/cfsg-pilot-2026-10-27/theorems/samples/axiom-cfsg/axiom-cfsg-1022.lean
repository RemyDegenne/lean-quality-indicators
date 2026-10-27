public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.LieType.Steinberg.Adjoint

open scoped MatrixGroups Matrix

section Frame

variable
  {L : Type} [Field L]

set_option maxRecDepth 100000 in
theorem g2_long_sigma : ∀ l ∈ Tag.G2.artifactRoots,
    iform (toVec Tag.G2.rank l) (toVec Tag.G2.rank l) = 6 →
      ∃ i j : Fin 3, i ≠ j ∧ toVec Tag.G2.rank l = g2Sigma i j := by
  decide +kernel

end Frame
end CFSG.HardMathSupport.Timmesfeld.CrossChar
end
