public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311r

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit
  CFSG.HardMathSupport.Lang.D4Three CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c
  CFSG.RankThree.PartOne.CTP CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator

section Frame

set_option linter.unusedSectionVars false

variable {K : Type} [Field K]

theorem isA2Type_conj_inputs2311r (ψ : MulAut ↥(adjointGroup Tag.D4 K)) {β : MulAut ↥(adjointGroup Tag.D4 K)}
    (h : IsA2Type β) : IsA2Type (ψ * β * ψ⁻¹) := by
  obtain ⟨φ, B, hB3, hB1, hφ⟩ := h
  refine ⟨φ * ψ⁻¹, B, hB3, hB1, ?_⟩
  rw [show φ * ψ⁻¹ * (ψ * β * ψ⁻¹) * (φ * ψ⁻¹)⁻¹ = φ * β * φ⁻¹ by group]
  exact hφ

end Frame
end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311r
end
