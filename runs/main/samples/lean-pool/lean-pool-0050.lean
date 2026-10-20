@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Johnson

section

open Filter Topology

open scoped Topology

namespace Asymptotics

theorem tendsto_complementShellWeight_ratio
    {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) :
    Tendsto
      (fun n : ℕ =>
        ((n - shellWeight a n : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (1 - a)) := by
  simpa only [shellWeight] using MetricCodes.Hamming.tendsto_complement_longitudinal_ratio ha ha'

end Asymptotics
end
end Johnson
end MetricCodes
end MetricCodesNoncomputable
end
