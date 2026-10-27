@[expose] public section

noncomputable section

open MeasureTheory

local instance classicalGeneratorMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance classicalGeneratorMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance classicalGeneratorProbabilityUnitAddCircle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Classical

open AVenhance.Infra.Parabolic.FourierGalerkin

open Homogenization

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def GalerkinGenerator.generatorClosedUnitCell : Set (Vec 2) :=
  Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)

end AVenhance.Infra.Classical
end
end
