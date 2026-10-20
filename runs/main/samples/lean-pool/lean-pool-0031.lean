@[expose] public section

section SourceQuantumChordWindow

namespace QuantumQueryComplexity

open scoped Matrix

open Matrix

variable {H : Type} [Fintype H] [DecidableEq H]

theorem effective_chord_gap_sq {P L : Matrix H H ℂ} (hP : IsQProjector P)
    (hL : IsQProjector L) {w : H → ℂ} (hw : L *ᵥ w = 0) (Δ : ℝ) :
    qNormSq (chordNearProj (qRefl P * qRefl L) Δ *ᵥ (P *ᵥ w))
      ≤ (Δ ^ 2 / 4) * qNormSq w := by
  set U := qRefl P * qRefl L with hUdef
  have hUu : U ∈ Matrix.unitaryGroup H ℂ :=
    mul_mem (qRefl_mem_unitaryGroup hP) (qRefl_mem_unitaryGroup hL)
  set N := chordNearProj U Δ with hNdef
  have hNcomm : N * (1 - U) = (1 - U) * N := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      chordNearProj_commute hUu]
  have hcore : (1 - U) *ᵥ w = (2 : ℂ) • (P *ᵥ w) := one_sub_qRefl_mul_qRefl_mulVec hw
  have key : (2 : ℂ) • (N *ᵥ (P *ᵥ w)) = (1 - U) *ᵥ (N *ᵥ w) := by
    calc (2 : ℂ) • (N *ᵥ (P *ᵥ w))
        = N *ᵥ ((2 : ℂ) • (P *ᵥ w)) := by rw [Matrix.mulVec_smul]
      _ = N *ᵥ ((1 - U) *ᵥ w) := by rw [hcore]
      _ = (N * (1 - U)) *ᵥ w := by rw [Matrix.mulVec_mulVec]
      _ = ((1 - U) * N) *ᵥ w := by rw [hNcomm]
      _ = (1 - U) *ᵥ (N *ᵥ w) := by rw [Matrix.mulVec_mulVec]
  have h4 : (4 : ℝ) * qNormSq (N *ᵥ (P *ᵥ w)) = qNormSq ((1 - U) *ᵥ (N *ᵥ w)) := by
    rw [← key, qNormSq_smul]
    norm_num
  have hbound := chordNear_bound_sq U Δ w
  have hproj := (isQProjector_chordNearProj U Δ).qNormSq_mulVec_le w
  nlinarith [sq_nonneg Δ, qNormSq_nonneg (N *ᵥ (P *ᵥ w)), qNormSq_nonneg w]

end QuantumQueryComplexity
end SourceQuantumChordWindow
end
