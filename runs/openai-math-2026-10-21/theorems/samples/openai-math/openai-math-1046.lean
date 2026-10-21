namespace OAI

open _root_.OAI.PlanarFalconer

section

section

open Set MeasureTheory

open scoped ComplexConjugate RealInnerProductSpace

namespace GraphLiteralSupport

namespace CurrentFalconer.DimensionalPolicy

open PlanarFalconer

theorem BranchStep.cost_nonneg {A : ℕ → ℝ} {N q offset : ℕ} {sig : ℝ}
    {s u : BranchState} {label : BranchLabel} (h : BranchStep A N q offset sig s label u)
    (hq : 0 < q) (hv : s.Valid N sig) : 0 ≤ branchCost A s label u := by
  have hn := h.nested hq hv
  cases h <;> simp only [branchCost]
  · exact sub_nonneg.mpr (intervalMin_le A le_rfl hn.2)
  · exact le_rfl
  · exact height_nonneg A hn.1
  · exact le_rfl
  · exact le_rfl
  · exact height_nonneg A hn.1

end CurrentFalconer.DimensionalPolicy
end GraphLiteralSupport
end
end
end OAI
