@[expose] public section

open Set

open scoped Topology ContDiff

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {V W V₁ W₁ : E → E} {s t : Set E} {x : E}

namespace VectorField

lemma lieBracket_smul_right {f : E → 𝕜} (hf : DifferentiableAt 𝕜 f x)
    (hW : DifferentiableAt 𝕜 W x) :
    lieBracket 𝕜 V (fun y ↦ f y • W y) x =
      (fderiv 𝕜 f x) (V x) • (W x) + (f x) • lieBracket 𝕜 V W x := by
  simp_rw [← differentiableWithinAt_univ, ← lieBracketWithin_univ, fderiv] at hW hf ⊢
  exact lieBracketWithin_smul_right hf hW uniqueDiffWithinAt_univ

end VectorField
end
end
