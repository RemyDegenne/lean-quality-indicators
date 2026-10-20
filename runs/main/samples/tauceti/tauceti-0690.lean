public section

namespace TauCeti

open MeasureTheory ProbabilityTheory Polynomial

open scoped NNReal ENNReal

theorem memLp_two_hermiteFunction (n : ℕ) : MemLp (hermiteFunction n) 2 volume := by
  rw [memLp_two_iff_integrable_sq (continuous_hermiteFunction n).aestronglyMeasurable]
  have hfun : (fun x => hermiteFunction n x ^ 2) = fun x =>
      ((hermiteDilated n) ^ 2).eval x
        * Real.exp (-x ^ 2)
        / Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) ^ 2 := by
    funext x
    have henv : Real.exp (-(x ^ 2 / 2)) ^ 2 = Real.exp (-x ^ 2) := by
      rw [pow_two, ← Real.exp_add]; congr 1; ring
    rw [hermiteFunction_def, div_pow, mul_pow, henv, eval_pow, eval_hermiteDilated]
  rw [hfun]
  exact (integrable_eval_mul_exp_neg_sq _).div_const _

end TauCeti
end
