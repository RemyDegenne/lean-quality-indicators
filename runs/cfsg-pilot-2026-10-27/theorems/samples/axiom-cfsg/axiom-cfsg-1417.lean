public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

section E6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Lattice CFSG.HardMathSupport.Timmesfeld.CrossChar

section Frames

open CFSG.RankThree.PartOne.KF4 CFSG.ClassicalInvolution.WeakCT
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Torality

open CFSG.RankThree.E6 (chain13 chain134 chainRoot support13 e6Index e6RootVec mem_support13
  isRoot_iff_exists_e6RootVec chainRoot_swap a2Equiv₁ a2Mat₁ coe_a2Rep₁ a2Equiv₁_apply
  e6TorusPair e6TorusPair_mem_subsystemGroup e6TorusPair_mem_torusGroup a2Mat₁_torus
  chainRoot134_mem_parabolicRoots a3RootFamily_all)

open Matrix

open scoped MatrixGroups

variable {L : Type} [Field L]

theorem e6FiveRho_range : (e6FiveRho L).range = subsystemGroup Tag.E6 L support13 := by
  ext g
  constructor
  · rintro ⟨X, rfl⟩
    exact ((a2Equiv₁ L).symm X).2
  · intro hg
    exact ⟨a2Equiv₁ L ⟨g, hg⟩, by simp [e6FiveRho]⟩

end Frames
end E6
end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
end
