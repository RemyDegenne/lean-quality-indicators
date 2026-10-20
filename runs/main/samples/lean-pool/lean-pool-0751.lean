@[expose] public section

noncomputable section

open Homogenization Set Filter

open scoped Topology

namespace AVenhance.Infra.Section4

open AVenhance.Infra.Flow

theorem amnrFlowSecondEval_continuousOn_forward
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (h k : Vec 2) (s T : ℝ) (hsT : s ≤ T) :
    ContinuousOn (amnrFlowSecondEval X s h k) (Icc s T ×ˢ univ) := by
  have hc := flow_secondVariation_jointContinuous_of_le hb hX h k s T hsT
  apply hc.congr
  intro z hz
  obtain ⟨_, _, B, hB, hD⟩ := exists_flow_spatialFDeriv_hasFDerivAt_of_le hb hX
    z.2 s z.1 hz.1.1
  change fderiv ℝ (fun y => fderiv ℝ (fun w => X z.1 w s) y) z.2 h k = _
  rw [hD.fderiv]
  exact hB h k

end AVenhance.Infra.Section4
end
end
