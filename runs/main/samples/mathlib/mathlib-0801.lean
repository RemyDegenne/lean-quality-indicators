@[expose] public section

open NormedField Set Filter

open scoped NNReal Pointwise Topology Uniformity

variable {R R' 𝕜 𝕜₂ 𝕜₃ 𝕝 E E₂ E₃ F ι : Type*}

export SeminormClass (map_smul_eq_mul)

namespace Seminorm

section SeminormedRing

variable [SeminormedRing 𝕜]

section AddCommGroup

variable [AddCommGroup E]

section Module

variable [Module 𝕜 E]

variable [SeminormedRing 𝕜₂] [AddCommGroup E₂] [Module 𝕜₂ E₂]

variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]

variable (p : Seminorm 𝕜 E)

theorem ball_zero_eq_preimage_ball {r : ℝ} : p.ball 0 r = p ⁻¹' Metric.ball 0 r := by
  rw [ball_zero_eq, preimage_metric_ball]

end Module
end AddCommGroup
end SeminormedRing
end Seminorm
end
