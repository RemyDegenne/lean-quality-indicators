@[expose] public section

noncomputable section

variable {𝕜 𝕜' E F G : Type*}

open NNReal Filter ENNReal Set Asymptotics

open scoped Topology Pointwise

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

namespace FormalMultilinearSeries

variable (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0}

theorem le_radius_of_bound (C : ℝ) {r : ℝ≥0} (h : ∀ n : ℕ, ‖p n‖ * (r : ℝ) ^ n ≤ C) :
    (r : ℝ≥0∞) ≤ p.radius :=
  le_iSup_of_le r <| le_iSup_of_le C <| le_iSup (fun _ => (r : ℝ≥0∞)) h

end FormalMultilinearSeries
end
end
