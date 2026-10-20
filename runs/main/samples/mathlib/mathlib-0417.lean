@[expose] public section

open Filter Function MeromorphicOn Metric Real Set

namespace ValueDistribution

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f g : 𝕜 → E} {a : WithTop E} {a₀ : E}

@[simp] theorem logCounting_add_const (hf : Meromorphic f) :
    logCounting (f + fun _ ↦ a₀) ⊤ = logCounting f ⊤ := by
  apply logCounting_add_analyticOn hf analyticOn_const

end ValueDistribution
end
