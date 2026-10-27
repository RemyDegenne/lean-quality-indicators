@[expose] public section

noncomputable section

namespace NavierStokes.SlowBorelBase

open Set Filter Function

open scoped Topology ContDiff BigOperators

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Positive sum, given by `SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) Prod.fst
(positiveCoefficient h f)`. -/
noncomputable def positiveSum (a : ℕ → ℕ) (h : ℝ) (f : ℕ → Inner → V) : Chart → V :=
  SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) Prod.fst (positiveCoefficient h f)

end NavierStokes.SlowBorelBase
end
end
