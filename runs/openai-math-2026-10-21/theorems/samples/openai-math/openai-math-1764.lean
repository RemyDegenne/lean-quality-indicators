namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem comparisonGraphLift_mem_degree (a : σ → ℕ) (ha : a ≠ 0) (x : F.layer a) :
    F.comparisonGraphLift π a ha x ∈ (F.comparisonFiltration π).layer (∑ i, a i) :=
  F.comparisonGraph_mem_layer π _ a ha le_rfl x

end Erdos3.MultidegreeLieFiltration
end
end OAI
