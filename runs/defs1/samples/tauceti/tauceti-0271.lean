public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace TauCeti.MeasureTheory

open scoped NNReal Topology Gradient InnerProductSpace

namespace TauCeti

namespace PDE

variable {n : ℕ}

/-- The coefficient field `κ(x) I` on `ℝⁿ⁺¹` with `κ(x) = 1` where `x₀ > 0` and `κ(x) = 2`
elsewhere: a uniformly elliptic matrix field with a jump across the hyperplane `{x₀ = 0}`. -/
def jumpCoefficient (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (if 0 < x 0 then 1 else 2 : ℝ) • 1

end PDE
end TauCeti
end
end
