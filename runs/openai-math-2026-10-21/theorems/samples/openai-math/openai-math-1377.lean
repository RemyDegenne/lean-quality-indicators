namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Chart

open scoped ContDiff Topology

open Set Function

variable {E F P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem conjugate_apply (c : OpenPartialHomeomorph E F) (hc : c.source = univ)
    (φ : E → E) (x : E) : conjugate c φ (c x) = c (φ x) := by
  have hx : x ∈ c.source := by rw [hc]; trivial
  rw [conjugate_of_mem c φ (c.map_source hx),c.left_inv hx]

end PackingSufficiencySupport.Chart
end
end OAI
