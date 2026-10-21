namespace OAI

namespace Falconer

open Set MeasureTheory

open scoped ContDiff

namespace SmoothSeparation

variable {X Y E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scaleTerms_value (S : SmoothSeparation X Y E) (c : S.index → ℂ)
    (x : X) (y : Y) (z : E) :
    (S.scaleTerms c).value x y z = ∑ i : S.index, c i*(S.left i x z*S.right i y z) := by
  apply Finset.sum_congr rfl
  intro i _
  exact mul_assoc _ _ _

end SmoothSeparation
end Falconer
end OAI
