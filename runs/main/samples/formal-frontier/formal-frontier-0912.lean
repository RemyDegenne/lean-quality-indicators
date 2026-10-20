@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

@[simp] lemma sphere2NorthVector_norm : ‖sphere2NorthVector‖ = 1 := by
  simp [sphere2NorthVector]

end SphereTopology
end
end
