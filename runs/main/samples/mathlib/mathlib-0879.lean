public section

open scoped NNReal

section NonUnital

variable {A : Type*} [NonUnitalRing A] [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]

variable [StarRing A] [TopologicalSpace A]

variable [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

namespace CFC

variable [PartialOrder A] [StarOrderedRing A]

variable [NonnegSpectrumClass ℝ A]

lemma posPart_eq_self (a : A) : a⁺ = a ↔ 0 ≤ a := by
  refine ⟨fun ha ↦ ha ▸ posPart_nonneg a, fun ha ↦ ?_⟩
  conv_rhs => rw [← cfcₙ_id ℝ a]
  rw [posPart_def]
  congr! 1 with x hx
  simpa [_root_.posPart_def] using quasispectrum_nonneg_of_nonneg a ha x hx

end CFC
end NonUnital
end
