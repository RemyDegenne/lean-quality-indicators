namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal

open scoped BigOperators NNReal

open scoped BigOperators

open scoped BigOperators InnerProductSpace

open Module

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

namespace CriticalSK

open scoped Topology

open scoped Topology

lemma edgeFixedCost_tendsto (h : ℝ) : Tendsto (edgeFixedCost h) atTop (𝓝 0) := by
  have hA := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 5/8)).const_mul
    (416*formConstant*(h+1))
  have hB := (tendsto_id.atTop_mul_atTop₀ Real.tendsto_sqrt_atTop).const_div_atTop (16:ℝ)
  have ht : Tendsto (fun L => edgeFixedCost h L) atTop (𝓝 0) := by
    simpa only [edgeFixedCost,neg_div,mul_zero,zero_add,id_eq] using hA.add hB
  exact ht

end CriticalSK
end
end OAI
