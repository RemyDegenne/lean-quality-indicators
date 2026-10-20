@[expose] public section

namespace Complex

open Filter Function MeromorphicOn Metric Real Set

open scoped ComplexConjugate Topology

variable {R : ℝ} {w : ℂ}

theorem meromorphicNFOn_canonicalFactor (h : w ∈ ball 0 R) :
    MeromorphicNFOn (canonicalFactor R w) Set.univ := by
  intro z hz
  obtain (rfl | h₁) := eq_or_ne z w
  · rw [meromorphicNFAt_iff_analyticAt_or]
    right
    refine ⟨meromorphic_canonicalFactor R z z, ?_, by simp⟩
    simpa [meromorphicOrderAt_canonicalFactor h] using WithTop.coe_lt_zero.mpr (by lia : -1 < 0)
  apply (analyticOnNhd_canonicalFactor R w z h₁).meromorphicNFAt

end Complex
end
