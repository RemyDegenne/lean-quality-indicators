@[expose] public section

open scoped Topology

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `IsIntegralCurveAt γ v t₀` means `γ : ℝ → E` is a local integral curve of `v` in a neighbourhood
containing `t₀`. -/
def IsIntegralCurveAt (γ : ℝ → E) (v : ℝ → E → E) (t₀ : ℝ) : Prop :=
  ∀ᶠ t in 𝓝 t₀, HasDerivAt γ (v t (γ t₀)) t

end
