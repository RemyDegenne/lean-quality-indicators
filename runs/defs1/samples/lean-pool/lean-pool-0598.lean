@[expose] public section

open Function Filter Set Metric

open scoped Topology NNReal Uniformity

namespace ExponentialJuliaSetMisiurewicz

noncomputable section

/-- Some forward image of `V` meets the real axis. -/
def EventuallyMeetsRealAxis (V : Set ℂ) : Prop :=
  ∃ n : ℕ, ∃ z ∈ V, OnRealAxis (expIterate n z)

end
end ExponentialJuliaSetMisiurewicz
end
