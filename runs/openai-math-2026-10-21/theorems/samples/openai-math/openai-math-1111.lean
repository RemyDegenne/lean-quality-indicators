namespace OAI

universe uE uV uΩ

noncomputable section

open MeasureTheory

open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON.SpinSystem

variable {n : ℕ} {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [NeZero n]

theorem norm_averageComplex_mul_mul_le (S : SpinSystem n V E)
    (a f g : C((V → Spin n), ℂ)) (c : ℝ) (hc : 0 ≤ c)
    (ha : ∀ σ, ‖a σ‖ ≤ c) :
    ‖S.averageComplexLinear (a*f*g)‖ ≤ c *
      (Real.sqrt (S.averageLinear (normObservable f * normObservable f)) *
       Real.sqrt (S.averageLinear (normObservable g * normObservable g))) := by
  have hpt : ∀ σ, normObservable (a*f*g) σ ≤
      (c • (normObservable f * normObservable g)) σ := by
    intro σ
    change ‖a σ*f σ*g σ‖ ≤ c * (‖f σ‖*‖g σ‖)
    rw [norm_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_right (ha σ) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  calc _ ≤ S.averageLinear (normObservable (a*f*g)) := S.norm_averageComplex_le _
       _ ≤ S.averageLinear (c • (normObservable f * normObservable g)) :=
          S.averageLinear_mono _ _ hpt
       _ = c * S.averageLinear (normObservable f * normObservable g) := by
          rw [map_smul, smul_eq_mul]
       _ ≤ _ := mul_le_mul_of_nonneg_left (S.averageLinear_mul_le_sqrt _ _) hc

end ClassicalON.SpinSystem
end
end OAI
