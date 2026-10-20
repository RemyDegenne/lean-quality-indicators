@[expose] public section

open CategoryTheory Convexity

open scoped BigOperators Simplicial

noncomputable section

namespace Convexity.StdSimplex

local instance stdSimplexMetricSpace (M : Type*) [Fintype M] :
    MetricSpace (StdSimplex ℝ M) :=
  Topology.IsEmbedding.comapMetricSpace (fun t : StdSimplex ℝ M ↦ (t.weights : M → ℝ))
    (isEmbedding_toFun_comp_weights ℝ M)

local instance stdSimplexIsConvexDist (M : Type*) [Fintype M] :
    IsConvexDist (StdSimplex ℝ M) where
  dist_iConvexComb_fst_snd_le f := by
    have hweights (g : (StdSimplex ℝ M × StdSimplex ℝ M) → StdSimplex ℝ M) :
        (f.iConvexComb g).weights =
          f.weights.sum (fun i r ↦ r • (g i).weights) := by
      simp [iConvexComb, Finsupp.sum_mapDomain_index, add_smul]
    rw [stdSimplex_dist_eq_weights, hweights, hweights, iConvexComb_eq_sum]
    convert (dist_iConvexComb_le (X := M → ℝ) f
      (fun p ↦ (p.1.weights : M → ℝ)) (fun p ↦ (p.2.weights : M → ℝ))) using 1 <;>
        simp only [iConvexComb_eq_sum]
    all_goals simp [stdSimplex_dist_eq_weights]

theorem affineSubdivision_iterate_support_vertexDiameter_le {m n N : ℕ}
    (c : AffineChain m n) (D : ℝ)
    (hc : ∀ a ∈ c.support, a.vertexDiameter ≤ D)
    {b : AffineSimplex m n}
    (hb : b ∈ ((affineSubdivision m n : AffineChain m n → AffineChain m n)^[N] c).support) :
    b.vertexDiameter ≤ ((n : ℝ) / (n + 1)) ^ N * D := by
  induction N generalizing b with
  | zero =>
      simpa using hc b hb
  | succ N ih =>
      rw [Function.iterate_succ_apply'] at hb
      obtain ⟨a, ha, hba⟩ := mem_support_affineSubdivision _ hb
      calc
        b.vertexDiameter ≤ (n : ℝ) / (n + 1) * a.vertexDiameter :=
          subdivideSimplex_support_vertexDiameter_le a hba
        _ ≤ (n : ℝ) / (n + 1) * (((n : ℝ) / (n + 1)) ^ N * D) :=
          mul_le_mul_of_nonneg_left (ih ha) (by positivity)
        _ = ((n : ℝ) / (n + 1)) ^ (N + 1) * D := by ring

end Convexity.StdSimplex
end
end
