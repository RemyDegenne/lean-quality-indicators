namespace OAI

section

section

noncomputable section

namespace LogConcaveSampling

open scoped Classical BigOperators RealInnerProductSpace NNReal

lemma dir_inner_map {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℕ} {A : E → Point d} {y : E} (hA : DifferentiableAt ℝ A y) (u : Point d) (v : E) :
    JetCalculus.dir v (fun z => inner ℝ u (A z)) y=inner ℝ u ((fderiv ℝ A y) v) := by
  unfold JetCalculus.dir
  change (fderiv ℝ ((innerSL ℝ u) ∘ A) y) v=_
  rw [((innerSL ℝ u).hasFDerivAt.comp y hA.hasFDerivAt).fderiv]
  rfl

end LogConcaveSampling
end
end
end
end OAI
