@[expose] public section

noncomputable section

namespace NavierStokes.NaturalAxisBridge

local instance instNaturalAxisBridge1 (I : AxisCoefficientSpace.Window) (ε : ℝ) :
    NormedAddCommGroup (AxisCoefficientSpace.AxisSpace I ε) := inferInstance

local instance instNaturalAxisBridge2 (I : AxisCoefficientSpace.Window) (ε : ℝ) :
    NormedSpace ℝ (AxisCoefficientSpace.AxisSpace I ε) := inferInstance

open Set Filter

open scoped Topology ContDiff

open AxisCoefficientSpace AxisWeightEstimates

/-- The pressure source in the complete coefficient space. -/
def pressureSource (I : Window) {ε : ℝ} (hε : 0 < ε)
    (a Φ : AxisSpace I ε) : AxisSpace I ε :=
  AxisOperators.product I hε (AxisOperators.product I hε a a)
    (AxisOperators.product I hε Φ Φ)

end NavierStokes.NaturalAxisBridge
end
end
