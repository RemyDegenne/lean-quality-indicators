public section

noncomputable section

open Filter Set

open scoped Topology

namespace SchauderBasis

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] (b : SchauderBasis 𝕜 E)

variable [CompleteSpace E]

theorem coe_dualBasis_proj (n : ℕ)
    (f : (Submodule.span 𝕜 (range b.coord)).topologicalClosure) :
    (b.dualBasis.proj n f : StrongDual 𝕜 E) = (f : StrongDual 𝕜 E).comp (b.proj n) := by
  rw [proj_apply, b.comp_proj_eq_sum]
  simp

end SchauderBasis
end
end
