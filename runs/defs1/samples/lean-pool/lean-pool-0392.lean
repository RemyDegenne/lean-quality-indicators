@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Homogenization AVenhance

open AVenhance.Infra.Ergodic

namespace AVenhance.Infra.Section5

local instance avInfraSection5HMinusToolsIsFiniteMeasure1 : IsFiniteMeasure (volume.restrict
    unitCube) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  unfold unitCube
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

/-- Exactly the time-norm carrier occurring in the BigBound statement. -/
def timeHMinusOneNorm (f : ℝ → Vec 2 → ℝ) : ENNReal :=
  (∫⁻ t in Set.Ioo (0 : ℝ) 1, hMinusOneNorm (f t) ^ 2) ^ (1 / 2 : ℝ)

end AVenhance.Infra.Section5
end
end
