namespace OAI

section

section

noncomputable section

open scoped BigOperators Topology

open MeasureTheory ProbabilityTheory Filter

noncomputable section

open MeasureTheory Set Filter

open scoped Topology Interval

noncomputable section

open MeasureTheory Set

open scoped Interval

noncomputable section

open MeasureTheory Set Filter ProbabilityTheory

open scoped Topology

namespace SK.Analytic

section GaussianDomination

variable {E F : Type} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem HasExpGrowth.gaussian_section_bound {f : E × ℝ → F} (hg : HasExpGrowth f) (R : ℝ) :
    ∃ b : ℝ → ℝ, Integrable b (gaussianReal 0 1) ∧
      ∀ x y, ‖x‖ ≤ R → ‖f (x,y)‖ ≤ b y := by
  obtain ⟨C,M,hC,hM,hg⟩ := hg
  refine ⟨fun y => C*Real.exp (M*R)*Real.exp (M*|y|),
    (integrable_exp_mul_abs_gaussian M).const_mul _, ?_⟩
  intro x y hx
  apply (hg (x,y)).trans
  change C * Real.exp (M*‖(x,y)‖) ≤ C*Real.exp (M*R)*Real.exp (M*|y|)
  rw [mul_assoc, ← Real.exp_add, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hM
  rw [Prod.norm_def, Real.norm_eq_abs]
  exact max_le (hx.trans (le_add_of_nonneg_right (abs_nonneg _)))
    (le_add_of_nonneg_left ((norm_nonneg x).trans hx))

end GaussianDomination
end SK.Analytic
end
end
end
end
end
end
end OAI
