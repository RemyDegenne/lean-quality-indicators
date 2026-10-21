namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory

open scoped BigOperators ContDiff ENNReal

open Set MeasureTheory

open scoped BigOperators ContDiff ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {τ : Type*} [Fintype τ]

lemma projectiveAxis_inner (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (v : E) :
    inner ℝ v (projectiveAxis f) = (WithLp.ofLp (f.symm v)).2 := by
  rw [← f.apply_symm_apply v]
  change inner ℝ (f (f.symm v)) (f (WithLp.toLp 2 (0,(1:ℝ)))) = _
  rw [f.inner_map_map]
  simp [WithLp.prod_inner_apply]

end AffineBernstein
end
end OAI
