@[expose] public section

noncomputable section

open MeasureTheory Set Filter

open Homogenization

open scoped Topology

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance.Infra.Parabolic.FourierGalerkin

open AVenhance.Infra.Parabolic.WeakUniqueness

local instance differenceFiniteUnitCube : IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
  refine ⟨?_⟩
  unfold AVenhance.unitCube
  rw [Measure.restrict_apply_univ, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

local instance differenceFiniteTimeCube :
    IsFiniteMeasure (volume.restrict AVenhance.timeCube) := by
  rw [forced_timeCube_measure_eq_product]
  infer_instance

theorem projection_sub_apply {θ θM : ℝ → Vec 2 → ℝ} {t : ℝ} (N : ℕ)
    (hθ : MemL2On AVenhance.unitCube (θ t)) (hM : MemL2On AVenhance.unitCube (θM t)) (x : Vec 2) :
    weakFourierModeProjection N (fun t x => θ t x - θM t x) t x =
      weakFourierModeProjection N θ t x - weakFourierModeProjection N θM t x := by
  rw [forced_projection_expansion, forced_projection_expansion, forced_projection_expansion,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [weakModePairing_sub hθ hM (forcedMode_memL2 N i)]
  ring

end AVenhance.Infra.Section5.RelativeError
end
end
