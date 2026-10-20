@[expose] public section

noncomputable section

open MeasureTheory Set Filter

open Homogenization

open scoped RealInnerProductSpace Topology

namespace AVenhance.Infra.Parabolic.FourierGalerkin

local instance timeFourierTestMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance timeFourierTestMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance timeFourierTestProbabilityUnitAddCircle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance timeFourierTestProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

local instance timeFourierTestCellFinite :
    IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  unfold AVenhance.unitCube
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

/-- The time derivative of a smooth spacetime test, as a spacetime function. -/
def spacetimeTestTimeDerivative (φ : ℝ → Vec 2 → ℝ) : ℝ → Vec 2 → ℝ :=
  fun t x => deriv (fun s => φ s x) t

end AVenhance.Infra.Parabolic.FourierGalerkin
end
end
