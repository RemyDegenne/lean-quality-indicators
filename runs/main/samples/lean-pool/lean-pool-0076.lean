@[expose] public section

open Filter MeasureTheory Set

open scoped ENNReal Topology

namespace QuadraticCarleson

namespace KaltonPaperApplication

open KaltonEndpoint

theorem monotone_partialCap_cap {X : Type*} (F : ℕ → X → ℝ≥0∞)
    (N : ℕ) (x : X) : Monotone (fun M ↦ partialCap F N M x) := by
  intro M M' hM
  apply Finset.sum_le_sum
  intro k hk
  exact min_le_min_right _ (Nat.cast_le.mpr hM)

end KaltonPaperApplication
end QuadraticCarleson
end
