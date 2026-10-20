@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

@[simp] lemma eastVector_norm : ‖eastVector‖ = 1 := by
  simp [eastVector]

end SphereTopology
end
end
