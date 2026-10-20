public section

noncomputable section

open Set MeasureTheory

open scoped Topology

namespace TauCeti.Green

theorem squaredFoldedGraphPath_mixedSigned_integral {U : Set ℂ} {P : ℂ → ℝ}
    (hL : Coordinate.im.graph (fun y ↦ y - 1) '' Icc 0 1 ⊆ U)
    (hR : Coordinate.im.graph (fun y ↦ 1 - y) '' Icc 0 1 ⊆ U) (hP : ContinuousOn P U) :
    BoundaryChain.Integrable Complex.imCLM P (-BoundaryChain.ofPath squaredFoldedGraphPath) ∧
      BoundaryChain.Integrable Complex.imCLM P (BoundaryChain.ofPath foldedGraphPath.symm) ∧
      BoundaryChain.integral Complex.imCLM P (-BoundaryChain.ofPath squaredFoldedGraphPath) =
        BoundaryChain.integral Complex.imCLM P (BoundaryChain.ofPath foldedGraphPath.symm) := by
  have h := squaredFoldedGraphPath_mixedSigned_nullChain hL hR
  have hi := BoundaryChain.integrable_neg_iff.mpr
    ((squaredFoldedGraphPath_subdivision hL hR).piecewiseGraphArc.integrable hP)
  rw [← Coordinate.proj_im]
  exact ⟨hi, (h.integrable_iff hP).mp hi, h.integral_eq hP⟩

end TauCeti.Green
end
end
