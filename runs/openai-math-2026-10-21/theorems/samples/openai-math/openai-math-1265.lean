namespace OAI

noncomputable section

open MeasureTheory Filter Matrix NormedSpace Metric Module Set

open scoped BigOperators Topology Matrix Matrix.Norms.Operator ENNReal

universe u uE uI

namespace SubpolynomialLp

open Metric Module Set

open scoped ENNReal

lemma dimension_packing_lower (p : ℝ) (hp : 1 < p) (n : ℕ) (hn : 2 ≤ n)
    (D : ℝ) (hD : 1 ≤ D) :
    Real.log (n:ℝ) / Real.log (1+2*D) ≤ (dimension.{u} p n D:ℝ) := by
  exact packing_lower_of_goodDimension p hp n _ hn D hD (dimension_good p hp n hn D hD)

end SubpolynomialLp
end
end OAI
