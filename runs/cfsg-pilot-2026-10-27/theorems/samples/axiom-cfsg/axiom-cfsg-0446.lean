public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator CFSG.HardMathSupport.Seitz.Proving

variable {K : Type} [Field K] [Finite K]

theorem closure_fixedSubgroup_frameD (hF : D4GraphA2FrameGen) (hK3 : ringChar K ≠ 3)
    (hK4 : 4 ≤ Nat.card K) :
    Subgroup.closure ((fixedSubgroup (gammaP K (orderThreeSL K)) :
      Set ↥(adjointGroup Tag.D4 K)) ∪ {frameD K (orderThreeSL K)}) = ⊤ := by
  rw [eq_top_iff, ← hF K hK3 hK4 (orderThreeSL K) (orderThreeSL_pow_three K)
    (orderThreeSL_ne_one K), Subgroup.closure_le]
  rintro g (hg | ⟨β, hβ, c, rfl | rfl⟩)
  · exact Subgroup.subset_closure (Or.inl hg)
  · exact (xPar_frame_mem_closure hK4 orderThreeSL_not_mem_center
      (exists_witness_orderThreeSL hK4) hβ c).1
  · exact (xPar_frame_mem_closure hK4 orderThreeSL_not_mem_center
      (exists_witness_orderThreeSL hK4) hβ c).2

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit
end
