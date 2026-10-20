@[expose] public section

open TopologicalSpace Set Function UniformSpace WithSeminorms

open scoped BoundedContinuousFunction Topology NNReal ContDiff

variable (𝕜 E F F' : Type*) [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedSpace 𝕜 F'] [SMulCommClass ℝ 𝕜 F']
  {n n₁ n₂ k : ℕ∞} {K K₁ K₂ : Compacts E}

scoped[Distributions] notation "𝓓^{" n "}_{" K "}(" E ", " F ")" =>
  ContDiffMapSupportedIn E F n K

scoped[Distributions] notation "𝓓_{" K "}(" E ", " F ")" =>
  ContDiffMapSupportedIn E F ⊤ K

open scoped Distributions

open ContDiffMapSupportedInClass

namespace ContDiffMapSupportedIn

variable {E F F'}

lemma fderivLM_apply_of_gt (f : 𝓓^{n}_{K}(E, F)) (hk : n < k + 1) :
    fderivLM 𝕜 n k f = 0 := by
  ext : 1
  simp [not_le_of_gt hk]

end ContDiffMapSupportedIn
end
