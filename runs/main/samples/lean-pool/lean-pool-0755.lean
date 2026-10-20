@[expose] public section

open Finset SimpleGraph Hypergraph

namespace Nibble.YusterE

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem triangleSub_linearSized_data_of_minDeg (D : ℕ) (hD : ∀ x, D ≤ G.degree x)
    (h2D : Fintype.card V ≤ 2 * D) {μ η d L : ℝ}
    (hη : 0 ≤ η) (hcodeg : 1 ≤ μ * d) (hbase : (Fintype.card V : ℝ) ≤ L * d)
    (hlo : (1 - μ) * d ≤ 2 * (D : ℝ) - (Fintype.card V : ℝ))
    (hhi : (Fintype.card V : ℝ) ≤ (1 + μ) * d) :
    NearlyRegularMost (triangleHypergraphSub G) d μ η ∧
      CodegreeBounded (triangleHypergraphSub G) (μ * d) ∧
      (∀ E : EdgeV G, (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) ≤ (1 + μ) * d) ∧
      (Fintype.card V : ℝ) ≤ L * d := by
  exact triangleSub_linearSized_data_of_window G hη hcodeg hbase
    (fun E => triangleSub_degree_window G E D hD h2D hlo hhi)

end Nibble.YusterE
end
