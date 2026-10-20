@[expose] public section

open scoped nonZeroDivisors Polynomial RatFunc WithZero

noncomputable section

namespace MarkoffRiemannRoch

open _root_.FunctionField

namespace FunctionField

open Chart

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

variable [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K]

theorem clifford {W : Divisor k K} (hW : IsCanonical k K W) (D : Divisor k K)
    (hdeg₀ : 0 ≤ D.deg) (hdeg₁ : D.deg ≤ 2 * (genus k K : ℤ) - 2)
    (hℓD : 0 < ell k K D) (hℓW : 0 < ell k K (W - D)) :
    2 * ((ell k K D : ℤ) - 1) ≤ D.deg := by
  have hW' := (isCanonical_iff_chart k K W).mp hW
  have hdeg₀' : 0 ≤ Chart.deg k K ((divisorEquivChart k K).symm D) := by
    simpa using hdeg₀
  have hdeg₁' : Chart.deg k K ((divisorEquivChart k K).symm D) ≤
      2 * (Chart.genus k K : ℤ) - 2 := by simpa [genus_eq_genusChart] using hdeg₁
  rw [ell_eq_chart k K D] at hℓD ⊢
  rw [ell_eq_chart k K (W - D)] at hℓW
  simpa [genus_eq_genusChart] using
    Chart.clifford k K hW' ((divisorEquivChart k K).symm D) hdeg₀' hdeg₁' hℓD hℓW

end FunctionField
end MarkoffRiemannRoch
end
end
