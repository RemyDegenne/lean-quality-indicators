public section

open scoped Matrix TensorProduct

namespace TauCeti

/-- Lorentz four-space as the real vector space of Hermitian two-by-two complex matrices. The
coordinate convention is compatible with `realCliffordThreeOneEvenEquivComplexMatrix`; the Spin
action becomes Hermitian congruence in `realSpinThreeOneEquivSpecialLinear_action`. -/
noncomputable def realCliffordThreeOneVectorEquivHermitian :
    (Fin 4 → ℝ) ≃ₗ[ℝ]
      selfAdjoint.submodule ℝ (Matrix (Fin 2) (Fin 2) ℂ) where
  toFun v := ⟨realCliffordThreeOneVectorMatrix v, by
    -- Restate subtype membership through the Hermitian predicate proved above.
    change IsSelfAdjoint (realCliffordThreeOneVectorMatrix v)
    exact (realCliffordThreeOneVectorMatrix_isHermitian v).isSelfAdjoint⟩
  invFun A := ![-(A.1 0 1).im, -(A.1 0 1).re,
    ((A.1 0 0).re - (A.1 1 1).re) / 2,
    ((A.1 0 0).re + (A.1 1 1).re) / 2]
  map_add' v w := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [realCliffordThreeOneVectorMatrix] <;> ring
  map_smul' r v := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [realCliffordThreeOneVectorMatrix] <;> ring
  left_inv v := by
    funext i
    fin_cases i <;> simp [realCliffordThreeOneVectorMatrix]
  right_inv A := by
    have h00 := Matrix.IsHermitian.apply A.2 0 0
    have h01 := Matrix.IsHermitian.apply A.2 1 0
    have h11 := Matrix.IsHermitian.apply A.2 1 1
    have h00im : (A.1 0 0).im = 0 := by
      have h := congrArg Complex.im h00
      simp at h
      linarith
    have h11im : (A.1 1 1).im = 0 := by
      have h := congrArg Complex.im h11
      simp at h
      linarith
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · apply Complex.ext
      · simp [realCliffordThreeOneVectorMatrix]
        ring
      · simp [realCliffordThreeOneVectorMatrix, h00im]
    · apply Complex.ext <;> simp [realCliffordThreeOneVectorMatrix]
    · -- Expose the matrix entry before using Hermitian symmetry across the diagonal.
      change realCliffordThreeOneVectorMatrix _ 1 0 = A.1 1 0
      rw [← h01]
      apply Complex.ext <;> simp [realCliffordThreeOneVectorMatrix]
    · apply Complex.ext
      · simp [realCliffordThreeOneVectorMatrix]
        ring
      · simp [realCliffordThreeOneVectorMatrix, h11im]

end TauCeti
end
