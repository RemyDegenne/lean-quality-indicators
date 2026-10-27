@[expose] public section

noncomputable section

open MeasureTheory

open scoped ENNReal

local instance galerkinMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance galerkinMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance galerkinProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Parabolic.FourierGalerkin

variable {n : ℕ}

/-- The ordinary dot product on `Vec 2`, written without importing PDE definitions. -/
def vecDot (u v : Fin 2 → ℝ) : ℝ := ∑ k, u k * v k

end AVenhance.Infra.Parabolic.FourierGalerkin
end
end
