public section

open Function Set

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {γ : ℝ → M} {v : (x : M) → TangentSpace I x} {s : Set ℝ} {t₀ : ℝ}

section Scaling

lemma IsMIntegralCurve.comp_mul (hγ : IsMIntegralCurve γ v) (a : ℝ) :
    IsMIntegralCurve (γ ∘ (· * a)) (a • v) := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn] at *
  exact hγ.comp_mul _

end Scaling
end
