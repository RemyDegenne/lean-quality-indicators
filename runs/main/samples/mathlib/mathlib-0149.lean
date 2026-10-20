@[expose] public section

variable {𝕜 E F G : Type*}

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

open NNReal Filter ENNReal Set Asymptotics

open scoped Topology Pointwise

section

variable {f g : E → F} {p pf : FormalMultilinearSeries 𝕜 E F} {s t : Set E} {x : E} {r r' : ℝ≥0∞}

variable (𝕜)

variable {𝕜}

lemma analyticOn_congr (hs : EqOn f g s) : AnalyticOn 𝕜 f s ↔ AnalyticOn 𝕜 g s :=
  ⟨fun h ↦ h.congr hs.symm, fun h ↦ h.congr hs⟩

end
end
