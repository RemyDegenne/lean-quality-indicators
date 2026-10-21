namespace OAI

section

namespace Erdos3

theorem maskedJointTupleBudget_le_exp (α : Type*) [Fintype α] [DecidableEq α]
    (N : ℕ) {W C w q : ℝ} (hW : 0 ≤ W) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hWw : W ≤ Real.exp w) (hCq : C ≤ Real.exp q) :
    maskedJointTupleBudget α N W C ≤ Real.exp (maskedJointTupleLog (Fintype.card α) N w q) := by
  have hNC : (N : ℝ)*C ≤ Real.exp ((N : ℝ)+q) := by
    rw [Real.exp_add]
    exact mul_le_mul (by linarith [Real.add_one_le_exp (N : ℝ)]) hCq hC (Real.exp_pos _).le
  have hsum : 2*scalarCubeGridBoundaryConstant α / MeasureTheory.volume.real (scalarCubeDomain α) + N*C ≤
      Real.exp (scalarCubeGridRatioLog (Fintype.card α)+((N : ℝ)+q)+1) := by
    calc
      _ ≤ 2*scalarCubeGridBoundaryConstant α / MeasureTheory.volume.real (scalarCubeDomain α) +
          Real.exp ((N : ℝ)+q) := by linarith
      _ ≤ _ := kernelTupleAllowance_le_exp α (show 0 ≤ (N : ℝ)+q by positivity)
  have hp : (W*C)^N ≤ Real.exp (N*(w+q)) := by
    rw [Real.exp_nat_mul, Real.exp_add]
    exact pow_le_pow_left₀ (mul_nonneg hW hC)
      (mul_le_mul hWw hCq hC (Real.exp_pos _).le) N
  have hB := (scalarCubeGridBoundaryConstant_pos α).le
  have hV := (scalarCubeDomain_volumeReal_pos α).le
  unfold maskedJointTupleBudget
  calc
    _ ≤ Real.exp (N*(w+q)) *
        Real.exp (scalarCubeGridRatioLog (Fintype.card α)+((N : ℝ)+q)+1) :=
      mul_le_mul hp hsum (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; unfold maskedJointTupleLog; ring

end Erdos3
end
end OAI
