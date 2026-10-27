@[expose] public section

noncomputable section

namespace NavierStokes.ActualPrimaryCovariance

open Set Function Filter

open scoped ContDiff Topology BigOperators

open CorrectionInitialization.ActualPrimary PartitionedCovariance PrimaryFieldAssembly

variable {B N0 : ℕ}

/-- Dyadic tail, given by `∑ᶠ n : ℕ, SquaredPartition.dyadicMask ((n + N : ℕ) : ℤ) q ^ 2`. -/
noncomputable def dyadicTail (N : ℕ) (q : ℝ) : ℝ :=
  ∑ᶠ n : ℕ, SquaredPartition.dyadicMask ((n + N : ℕ) : ℤ) q ^ 2

end NavierStokes.ActualPrimaryCovariance
end
end
