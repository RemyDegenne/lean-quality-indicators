@[expose] public noncomputable section

open scoped Nat NNReal ContDiff

variable {ι 𝕜 𝕜' D E F G H V : Type*}

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

scoped[SchwartzMap] notation "𝓢(" E ", " F ")" => SchwartzMap E F

namespace SchwartzMap

section Comp

variable (𝕜)

variable [RCLike 𝕜]

variable [NormedAddCommGroup D] [NormedSpace ℝ D]

variable [NormedSpace 𝕜 F]

/-- Composition with a function on the right is a continuous linear map on Schwartz space
provided that the function is temperate and antilipschitz. -/
def compCLMOfAntilipschitz {K : ℝ≥0} {g : D → E}
    (hg : g.HasTemperateGrowth) (h'g : AntilipschitzWith K g) :
    𝓢(E, F) →L[𝕜] 𝓢(D, F) := by
  refine compCLM 𝕜 hg ⟨1, K * max 1 ‖g 0‖, fun x ↦ ?_⟩
  calc
  ‖x‖ ≤ K * ‖g x - g 0‖ := by
    rw [← dist_zero_right, ← dist_eq_norm]
    apply h'g.le_mul_dist
  _ ≤ K * (‖g x‖ + ‖g 0‖) := by
    gcongr
    exact norm_sub_le _ _
  _ ≤ K * (‖g x‖ + max 1 ‖g 0‖) := by
    gcongr
    exact le_max_right _ _
  _ ≤ (K * max 1 ‖g 0‖ : ℝ) * (1 + ‖g x‖) ^ 1 := by
    simp only [mul_add, add_comm (K * ‖g x‖), pow_one, mul_one, add_le_add_iff_left]
    gcongr
    exact le_mul_of_one_le_right (by positivity) (le_max_left _ _)

end Comp
end SchwartzMap
end
