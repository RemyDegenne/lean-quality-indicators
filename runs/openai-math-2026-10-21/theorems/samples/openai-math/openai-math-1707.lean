namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set

open scoped NNReal ENNReal

open Set Filter

open scoped Topology

open MeasureTheory ProbabilityTheory Filter Set

open scoped ENNReal NNReal Topology BigOperators

open MeasureTheory Filter Set

open scoped ENNReal NNReal BigOperators

open MeasureTheory ProbabilityTheory Set Filter

open scoped ENNReal NNReal Topology

open scoped NNReal ENNReal Topology

open scoped NNReal Topology

open Set

open Set Filter MeasureTheory

open scoped BigOperators

open scoped Topology NNReal

open scoped Topology BigOperators

open scoped ENNReal NNReal

open MeasureTheory Set

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal BigOperators Classical

open Classical

open scoped ENNReal NNReal Topology BigOperators MatrixOrder

open scoped NNReal BigOperators

open MeasureTheory Metric Set

open Metric

open scoped RealInnerProductSpace

open Filter

namespace MicroscopicJamming

lemma norm_rescale_sq {n : ℕ} {y : SpinSpace n} (hy : ‖y‖ = 1) :
    ‖Real.sqrt n • y‖^2 = (n:ℝ) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), hy, mul_one,
    Real.sq_sqrt (Nat.cast_nonneg _)]

end MicroscopicJamming
end
end OAI
