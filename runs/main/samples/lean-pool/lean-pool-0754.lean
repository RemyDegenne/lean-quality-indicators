public section

open Function Metric Set

open scoped Topology

namespace SeveralComplexVariables

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

section Figure

variable {ι : Type*} [Fintype ι]

theorem hartogsFigure_eq_of_isEmpty [IsEmpty ι] {r : ℝ} (hr : 0 < r) (s : ℝ) :
    hartogsFigure (ι := ι) r s = ball 0 1 ×ˢ ball 0 1 := by
  ext z
  simp only [hartogsFigure, mem_union, mem_prod, Subsingleton.elim z.1 (0 : ι → ℂ),
    mem_ball, dist_self, hr, dist_zero_right, true_and, zero_lt_one, mem_sdiff,
    mem_closedBall, not_le, or_iff_left_iff_imp, and_imp]
  exact fun h _ => h

end Figure
end SeveralComplexVariables
end
