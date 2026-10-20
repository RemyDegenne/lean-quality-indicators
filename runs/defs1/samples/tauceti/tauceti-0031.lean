public section

noncomputable section

open Filter Matrix.ProjectiveSpecialLinearGroup Metric MulAction Set Topology UpperHalfPlane

open scoped MatrixGroups Pointwise

namespace Subgroup

open TauCeti

variable (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) (ε : ℝ)

/-- The hyperbolic disc of radius `ε` about `z`, as a set invariant under the stabilizer of `z`
in `Γ`: that stabilizer acts by hyperbolic isometries fixing `z`. -/
def stabilizerBall : SubMulAction (stabilizer Γ z) ℍ where
  carrier := ball z ε
  smul_mem' q τ hτ := by
    have hq : ((q : Γ) : PSL(2, ℝ)) • z = z := by
      have h := q.2
      rwa [mem_stabilizer_iff, Subgroup.smul_def] at h
    have hball : ((q : Γ) : PSL(2, ℝ)) • ball z ε = ball z ε := by
      rw [Metric.smul_ball, hq]
    simp only [Subgroup.smul_def]
    exact hball ▸ Set.smul_mem_smul_set hτ

end Subgroup
end
end
