public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open scoped MatrixGroups

section

theorem xUnit_mem_subsystemGroup13 (L : Type) [Field L] {i : Fin Tag.E8.rank}
    (hi : i ∈ e8support13) (c : L) : xUnit Tag.E8 L i c ∈ subsystemGroup Tag.E8 L e8support13 :=
  Subgroup.subset_closure ⟨i, hi, c, Or.inl rfl⟩

end
end CFSG.HardMathSupport.Timmesfeld.CrossChar
end
