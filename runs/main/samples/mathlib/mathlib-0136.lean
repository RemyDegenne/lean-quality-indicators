public section

open Metric Set Function Filter

open scoped NNReal Topology

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

variable [NontrivialTopology E]

section Surj

variable (E)

theorem nnnorm_surjective : Surjective (nnnorm : E → ℝ≥0) := fun c =>
  (exists_norm_eq E c.coe_nonneg).imp fun _ h => NNReal.eq h

end Surj
end Seminormed
end
