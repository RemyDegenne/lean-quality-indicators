namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset

open scoped ENNReal NNReal BoundedContinuousFunction

open Finset MeasureTheory Filter Topology

open scoped BigOperators

open Finset Matrix

open scoped Matrix.Norms.L2Operator

open Matrix

namespace SmoothObstruction.ManifoldCoordinates

open Set Metric MeasureTheory Filter Topology

open scoped Manifold ContDiff

variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    {ι : Type*} [Fintype ι]

theorem uniform_original_shadow (hclosed : IsClosed (range I))
    (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
    {ε : ℝ} (hε : 0<ε) :
    ∃ σ : ℝ,0<σ ∧ ∀ (S : Diffeomorph I I M M ∞) (c : M → ι)
      (n : ℕ) (ρ : ℝ) (x z : M), (∀ u,u∈K (c u)) → ρ≤σ →
      originalTube I S a c (n:=n) ρ x z →
      ∀ t : Fin (n+1),dist (S^[t.val] z) (S^[t.val] x)<ε := by
  obtain ⟨σ,hσ,hm⟩ := CoordinateTubes.uniform_inverse_modulus I hclosed a K hK hKU hε
  refine ⟨σ,hσ,?_⟩
  intro S c n ρ x z hc hρ ht t
  exact hm _ _ (hc _) _ (ht t).1 ((ht t).2.trans hρ)

end SmoothObstruction.ManifoldCoordinates
end
end OAI
