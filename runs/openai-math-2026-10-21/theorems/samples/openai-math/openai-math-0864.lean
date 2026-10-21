namespace OAI

open Set Metric Filter MeasureTheory

open scoped Topology

noncomputable section

namespace RegularPointCoordinates

theorem local_midpoint_density_eq {n : ℕ} (hn : 0 < n)
    (μ : FiniteMeasure (Euclidean n)) (hμ : (μ : Measure (Euclidean n)) ≪ volume)
    (z : Euclidean n) {δ : ℝ} (hδ : 0 < δ)
    (hc : ∀ u ∈ ball z δ, ∀ v ∈ ball z δ, ∀ r : ℝ, 0 < r → r ≤ δ →
      (1/2:ℝ)^n*(μ : Measure (Euclidean n)).real (ball v r) ≤
        (μ : Measure (Euclidean n)).real (closedBall ((1/2:ℝ) • (u+v)) (r/2)))
    {x y : Euclidean n} (hx : x ∈ ball z (δ/4)) (hy : y ∈ ball z (δ/4))
    {a b : ℝ}
    (hlimx : Tendsto (fun r => (μ : Measure (Euclidean n)).real (closedBall x r)/
      volume.real (closedBall x r)) (𝓝[>] 0) (𝓝 a))
    (hlimy : Tendsto (fun r => (μ : Measure (Euclidean n)).real (closedBall y r)/
      volume.real (closedBall y r)) (𝓝[>] 0) (𝓝 b)) : a = b :=
  le_antisymm (local_midpoint_density_le hn μ hμ z hδ hc hx hy hlimx hlimy)
    (local_midpoint_density_le hn μ hμ z hδ hc hy hx hlimy hlimx)

end RegularPointCoordinates
end
end OAI
