@[expose] public section

local macro_rules | `($x ^ $n:num) => `($x ^ ($n : ℕ))

noncomputable section

namespace NavierStokes.ActivationCone

open Set Filter

open scoped Topology ContDiff

open ConeAlgebra StressActivation ProfileHistories

/-- Activated stress as an element of `ℝ × ℝ`. -/
noncomputable def activatedStress (h X0 : ℝ) (initial : HistoryRow → ℝ → ℝ)
    (L U : ProfileHistories.Field) (T κ : ℝ) (p : Point) : ℝ × ℝ :=
  (activatedAngular T κ L p * (activatedStockOne h X0 initial L U T κ p - actualP1 T κ L p),
    activatedAngular T κ L p * (activatedStockTwo h X0 initial L U T κ p - actualP2 T κ X0 L U p))

end NavierStokes.ActivationCone
end
end
