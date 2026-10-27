@[expose] public section

namespace AVenhance.Infra.Ergodic

open MeasureTheory

noncomputable section

local instance avInfraErgodicPeriodicMeasureSpace1 : MeasureSpace UnitAddCircle :=
    ⟨AddCircle.haarAddCircle⟩

local instance avInfraErgodicPeriodicMeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure (volume :
    Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance avInfraErgodicPeriodicIsProbabilityMeasure3 : IsProbabilityMeasure (volume :
    Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The normalized average of a Euclidean function over the unit torus,
computed using its canonical representative in `(0,1]^d`. -/
def cellAverage {d : ℕ} (f : Homogenization.Vec d → ℝ) : ℝ :=
  ∫ x : UnitTorus d, torusFunction f x

end
end AVenhance.Infra.Ergodic
end
