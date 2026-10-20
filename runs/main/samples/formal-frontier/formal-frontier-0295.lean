@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

@[simp] lemma sphere2NorthPoint_third : ((sphere2NorthPoint : E3) 2) = 1 := by
  simp [sphere2NorthPoint, sphere2NorthVector]

end SphereTopology
end
end
