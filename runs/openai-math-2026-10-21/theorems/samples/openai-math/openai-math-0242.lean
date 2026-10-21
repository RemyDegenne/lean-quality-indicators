namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

open scoped TensorProduct BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem realComparisonLog_eval (p : F.realification.adaptedLieSubalgebra) (x : σ → ℚ) :
    eval x (F.realComparisonLog π p) =
      ∑ a ∈ (coefficients p.val).support,
        (a.prod fun i n => x i ^ n) • F.realComparisonCoefficient π p a := by
  simp only [realComparisonLog, map_sum, eval_monomial]

end Erdos3.MultidegreeLieFiltration
end
end OAI
