namespace OAI

namespace MetricKMedianRecovery.LocalSearch

variable {V : Type*} [PseudoMetricSpace V]

lemma cost_nonneg (D S : Finset V) : 0 ≤ cost D S :=
  Finset.sum_nonneg (fun _ _ => connection_nonneg _ _)

end MetricKMedianRecovery.LocalSearch
end OAI
