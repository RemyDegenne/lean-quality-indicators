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

/-- Invariance under translations in `N⁻¹ℤ^d`. -/
def IsFastPeriodic {d : ℕ} (N : ℕ) (f : Homogenization.Vec d → ℝ) : Prop :=
  ∀ (x : Homogenization.Vec d) (k : Fin d → ℤ),
    f (x + fun i => (k i : ℝ) / (N : ℝ)) = f x

end
end AVenhance.Infra.Ergodic
end
