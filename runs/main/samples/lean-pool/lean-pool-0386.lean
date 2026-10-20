@[expose] public section

namespace Matrix

variable {n 𝕜 : Type _} [RCLike 𝕜] [Fintype n] [DecidableEq n]

open scoped Matrix BigOperators ComplexOrder MatrixOrder

theorem _root_.Matrix.PosSemidef.rpow_mul_rpow (r₁ r₂ : NNRealˣ) {Q : Matrix n n 𝕜}
    (hQ : PosSemidef Q) :
    hQ.rpow r₁ * hQ.rpow r₂ = hQ.rpow (r₁ + r₂) := by
  simp_rw [PosSemidef.rpow, IsHermitian.rpow, ← innerAut.map_mul, Pi.pow_def,
    diagonal_mul_diagonal, Function.comp_apply, ← RCLike.ofReal_mul]
  congr
  ext i
  simp only [Function.comp_apply]
  by_cases h : hQ.1.eigenvalues i = 0
  · simp_rw [h]
    have hr₁ : (r₁ : ℝ) ≠ 0 := by
      exact_mod_cast Units.ne_zero r₁
    have hr₂ : (r₂ : ℝ) ≠ 0 := by
      exact_mod_cast Units.ne_zero r₂
    have hsum : ((r₁ : ℝ) + (r₂ : ℝ)) ≠ 0 := by
      intro hsum
      have hnn : ((r₁ : NNReal) + (r₂ : NNReal)) = 0 := by
        exact_mod_cast hsum
      exact Units.ne_zero r₁ (add_eq_zero.mp hnn).1
    simp [Real.zero_rpow, hr₁, hr₂, hsum]
  · rw [← Real.rpow_add]
    apply lt_of_le_of_ne (hQ.eigenvalues_nonneg _)
    rwa [ne_eq, eq_comm]

end Matrix
end
