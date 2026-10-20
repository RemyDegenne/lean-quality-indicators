@[expose] public section

open NormedField Set

open scoped Pointwise Topology NNReal

noncomputable section

variable {𝕜 E : Type*}

section AddCommGroup

variable [AddCommGroup E] [Module ℝ E]

variable {s t : Set E} {x : E} {a : ℝ}

open Filter

section RCLike

variable [RCLike 𝕜] [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E]

variable {hs₀ : Balanced 𝕜 s} {hs₁ : Convex ℝ s} {hs₂ : Absorbent ℝ s} [TopologicalSpace E]
  [ContinuousSMul ℝ E]

theorem gaugeSeminorm_ball_one (hs : IsOpen s) : (gaugeSeminorm hs₀ hs₁ hs₂).ball 0 1 = s := by
  rw [Seminorm.ball_zero_eq]
  exact setOfPred_gauge_lt_one_eq_self_of_isOpen hs₁ hs₂.zero_mem hs

end RCLike
end AddCommGroup
end
end
