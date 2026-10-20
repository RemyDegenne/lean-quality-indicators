public noncomputable section

open MulAction

open scoped MatrixGroups

namespace Subgroup

variable {Δ Γ : Subgroup PSL(2, ℝ)} [Δ.IsFiniteRelIndex Γ]

variable (h : Δ ≤ Γ)

theorem cuspOrbitMap_surjective : Function.Surjective (cuspOrbitMap h) := by
  intro C
  obtain ⟨c, rfl⟩ := cuspOrbitMk_surjective C
  refine ⟨Δ.cuspOrbitMk
    ⟨c, mem_cuspPoints.mpr (IsCuspPoint.of_isFiniteRelIndex
      (mem_cuspPoints.mp c.property))⟩, ?_⟩
  simp

end Subgroup
end
