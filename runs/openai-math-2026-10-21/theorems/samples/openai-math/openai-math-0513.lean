namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem realAdditiveTripleProjection_coord (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (j : Fin 3)
    (g : (F.additiveTripleFiltration i hi c hc).realification.Group) :
    (F.realAdditiveTripleProjection i hi c hc j g).coord =
      tripleToPi (F.realifiedAdditiveTripleEquiv i hi c hc g.coord).val j :=
  (F.realifiedAdditiveTripleEquiv_projection i hi c hc j g.coord).symm

end Erdos3.MultidegreeLieFiltration
end
end OAI
