@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

section

open Filter Metric Topology

open scoped BigOperators InnerProductSpace Topology

namespace Hamming

theorem binaryRate_le_of_eventually {δ r : ℝ} {u : ℕ → ℝ}
    (hu : Tendsto u atTop (nhds r))
    (hbound : ∀ᶠ n : ℕ in atTop,
      Real.logb 2
        (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) / (n : ℝ) ≤ u n) :
    binaryRate δ ≤ r := by
  let w : ℕ → ℝ := fun n =>
    Real.logb 2
      (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) / (n : ℝ)
  have hlower : atTop.IsBoundedUnder (· ≥ ·) w :=
    Filter.isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall (codeLogRate_nonneg δ))
  have hcob : atTop.IsCoboundedUnder (· ≤ ·) w :=
    hlower.isCoboundedUnder_le
  have hcomparison : Filter.limsup w atTop ≤ Filter.limsup u atTop :=
    Filter.limsup_le_limsup hbound hcob hu.isBoundedUnder_le
  change Filter.limsup w atTop ≤ r
  exact hcomparison.trans_eq hu.limsup_eq

end Hamming
end
end MetricCodes
end MetricCodesNoncomputable
end
