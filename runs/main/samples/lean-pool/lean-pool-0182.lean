@[expose] public section

noncomputable section

open Homogenization

open Filter

open AVenhance.Infra.Section4

open scoped Topology

namespace AVenhance.Infra.Section4

theorem ThetaDifferentiated.theta_transport_contDiff {b : Vec 2 → Vec 2}
    {u : Vec 2 → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (classicalTransport b u) := by
  unfold classicalTransport
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => ∑ j : Fin 2, b x j * AVenhance.spaceGrad u x j)
  apply ContDiff.sum
  intro j hj
  exact ((contDiff_pi.1 hb) j).mul (ThetaDifferentiated.thetaSpaceGradComponent_contDiff hu j)

end AVenhance.Infra.Section4
end
end
