namespace OAI

section

section

namespace MetricKMedian.Certificates

open Analytic

theorem pSeries_eq (X : ℝ) : pSeries X = pTaylor 13 (1 - X) := by
  norm_num [pSeries, pTaylor, Finset.sum_range_succ, Nat.factorial]
  ring

end MetricKMedian.Certificates
end
end
end OAI
