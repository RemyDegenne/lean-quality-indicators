public section

open scoped lp ENNReal NNReal Topology

open Filter

namespace lp

variable {ι 𝕜 : Type*} [NontriviallyNormedField 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

@[simp]
theorem diagonalCLM_zero : diagonalCLM (p := p) (0 : ℓ^∞(ι, 𝕜)) = 0 := by
  ext x i
  simp

end lp
end
