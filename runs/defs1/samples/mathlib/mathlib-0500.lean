@[expose] public noncomputable section

open scoped Nat NNReal ContDiff

variable {ι 𝕜 𝕜' D E F G H V : Type*}

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

scoped[SchwartzMap] notation "𝓢(" E ", " F ")" => SchwartzMap E F

namespace SchwartzMap

section HasCompactSupport

/-- A smooth compactly supported function is a Schwartz function. -/
@[simps]
def _root_.HasCompactSupport.toSchwartzMap {f : E → F} (h₁ : HasCompactSupport f)
    (h₂ : ContDiff ℝ ∞ f) : 𝓢(E, F) where
  toFun := f
  smooth' := h₂
  decay' k n := by
    set g := fun x ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖
    have hg₁ : Continuous g := by
      apply Continuous.mul (by fun_prop)
      exact (h₂.of_le (mod_cast le_top)).continuous_iteratedFDeriv'.norm
    have hg₂ : HasCompactSupport g := (h₁.iteratedFDeriv _).norm.mul_left
    obtain ⟨x₀, hx₀⟩ := hg₁.exists_forall_ge_of_hasCompactSupport hg₂
    exact ⟨g x₀, hx₀⟩

end HasCompactSupport
end SchwartzMap
end
