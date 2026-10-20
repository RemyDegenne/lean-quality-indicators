@[expose] public section

namespace BeyondBethe

/-- Run Bethe bisection for the explicit iteration budget from its prescribed initial state. -/
def explicitBetheOptimizerState {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) :
    BetheBisectionState (m * m + 1) :=
  runBetheBisection (explicitRegularizationScale (m + 1)) A
    (explicitOptimizerPrecision A) (explicitOptimizerFloor A)
    (explicitOptimizerInnerRadius A) (explicitOptimizerBisectionSteps A)
    (explicitBetheOptimizerInitialState A)

end BeyondBethe
end
