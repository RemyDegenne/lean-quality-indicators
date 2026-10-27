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

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def TimeDependentFourierTest.timeFourierTestCellClosure : Set (Vec 2) :=
  Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1

end AVenhance.Infra.Parabolic.FourierGalerkin
end
end
