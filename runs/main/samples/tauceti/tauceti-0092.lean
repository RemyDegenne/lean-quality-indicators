public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {i₀ : ι}

theorem ae_dirichletNormalize_sum_eq_dirichletChart (a r : ι → ℝ) (i₀ : ι) :
    (fun x ↦ (dirichletNormalize x, ∑ i, x i)) =ᵐ[Measure.pi fun i ↦ gammaMeasure (a i) (r i)]
      (fun z ↦ (dirichletChart i₀ z.2, z.1)) ∘ dirichletChartCoords i₀ ∘
        ⇑(Equiv.piSplitAt i₀ fun _ : ι ↦ ℝ) := by
  have : Nonempty ι := ⟨i₀⟩
  filter_upwards [ae_pos_sum_pi_gammaMeasure a r] with x hx
  apply Prod.ext
  · exact dirichletNormalize_eq_dirichletChart i₀ hx.ne'
  · simp [Function.comp_apply, Equiv.piSplitAt_apply,
      ← Fintype.sum_eq_add_sum_subtype_ne (fun i ↦ x i) i₀]

end Probability
end TauCeti
end
end
