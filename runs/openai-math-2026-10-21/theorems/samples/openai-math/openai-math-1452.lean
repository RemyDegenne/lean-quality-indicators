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

open Finset Set

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal BigOperators Topology

open MeasureTheory ProbabilityTheory Filter Metric

open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

open scoped BigOperators Classical

open scoped ENNReal NNReal Topology BigOperators Matrix MatrixOrder

open scoped BigOperators RealInnerProductSpace

open scoped NNReal Topology BigOperators

open scoped NNReal BigOperators RealInnerProductSpace

open scoped ENNReal NNReal BigOperators MatrixOrder

open scoped MatrixOrder

open scoped NNReal

open scoped BigOperators NNReal

open scoped NNReal ENNReal BigOperators Topology

open scoped Topology ENNReal NNReal

open scoped Matrix.Norms.L2Operator MatrixOrder Topology NNReal ENNReal BigOperators

open scoped Topology ENNReal NNReal BigOperators MatrixOrder Matrix.Norms.L2Operator

open scoped Topology NNReal ENNReal BigOperators

open scoped BigOperators NNReal Topology

open scoped Topology NNReal ENNReal BigOperators MatrixOrder

open scoped Topology NNReal ENNReal BigOperators MatrixOrder Matrix.Norms.L2Operator

open MeasureTheory ProbabilityTheory Set Filter

open scoped Topology NNReal ENNReal BigOperators

open MeasureTheory ProbabilityTheory Set Filter

open scoped Topology NNReal ENNReal BigOperators

open MeasureTheory ProbabilityTheory Set Filter

open scoped Topology NNReal ENNReal BigOperators

open MeasureTheory ProbabilityTheory Set Filter

open scoped Topology NNReal ENNReal BigOperators

open MeasureTheory ProbabilityTheory Set Filter

open scoped Topology NNReal ENNReal BigOperators

open MeasureTheory ProbabilityTheory Set Filter

open scoped Topology NNReal ENNReal BigOperators

open MeasureTheory ProbabilityTheory Set Filter

open scoped Topology

open MeasureTheory ProbabilityTheory Set Filter

open scoped Topology BigOperators

namespace MicroscopicJamming

lemma gaussianRankProfile_bound (rs : List (ℝ × ℝ)) (s : ℝ) :
    |gaussianRankProfile rs s| ≤ (rs.map (fun r => |r.2|)).sum := by
  induction rs with
  | nil => simp [gaussianRankProfile]
  | cons r rs ih =>
    rw [gaussianRankProfile_cons]
    simp only [List.map_cons,List.sum_cons]
    refine (abs_add_le _ _).trans (add_le_add ?_ ih)
    split_ifs <;> simp [abs_nonneg]

end MicroscopicJamming
end
end OAI
