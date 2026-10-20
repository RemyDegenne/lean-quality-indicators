@[expose] public section

noncomputable section

open MeasureTheory Set

open Homogenization

open AVenhance.Infra.Parabolic.FourierGalerkin

local instance classicalSmoothCoefficientsMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance classicalSmoothCoefficientsMeasureIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance classicalSmoothCoefficientsProbability : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance classicalSmoothCoefficientsTorusProbability : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

namespace AVenhance.Infra.Classical

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def GalerkinSmoothCoefficients.classicalCoefficientClosedCell : Set (Vec 2) :=
  Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)

end AVenhance.Infra.Classical
end
end
