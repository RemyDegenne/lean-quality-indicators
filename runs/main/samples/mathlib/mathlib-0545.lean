@[expose] public section

noncomputable section

open Set Fin Filter Function

open scoped NNReal Topology ContDiff

universe u uE uF uG uX

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type uE} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {s s₁ t u : Set E} {f f₁ : E → F} {x : E} {m n : ℕ∞ω}
  {p : E → FormalMultilinearSeries 𝕜 E F}

theorem contDiff_all_iff_nat : (∀ n : ℕ∞, ContDiff 𝕜 n f) ↔ ∀ n : ℕ, ContDiff 𝕜 n f := by
  simp only [← contDiffOn_univ, contDiffOn_all_iff_nat]

end
end
