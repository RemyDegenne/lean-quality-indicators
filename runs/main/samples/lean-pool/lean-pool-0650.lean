@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

section

open Filter Metric Topology

open scoped BigOperators InnerProductSpace Topology

namespace Hamming

theorem binaryRate_le_of_positive_feasible_bound {δ a b : ℝ}
    (h : Feasible δ a b) (hb : 0 < b)
    (hbound : ∀ᶠ n : ℕ in atTop,
      (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) ≤
        spectralPrefactor δ a b * windowFibreQuotient a b n) :
    binaryRate δ ≤ MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b := by
  exact binaryRate_le_of_eventually_windowFibreQuotient
    hb h.2.1 h.2.2.1 (spectralPrefactor_pos h) hbound

end Hamming
end
end MetricCodes
end MetricCodesNoncomputable
end
