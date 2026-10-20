@[expose] public section

open MeasureTheory Metric Set Filter

open Topology

open scoped ENNReal NNReal

noncomputable section

variable {n : ℕ}

section Balls

variable {n : ℕ}

lemma measure_ball_pos_of_mem_support {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {a : EuclideanSpace ℝ (Fin n)} (ha : a ∈ μ.support) {ρ : ℝ} (hρ : 0 < ρ) :
    0 < μ (ball a ρ) :=
  (Measure.mem_support_iff_forall a).mp ha _ (ball_mem_nhds a hρ)

end Balls
end
end
