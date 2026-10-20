@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

@[simp] lemma circlePunctureIntersectionRepresentative_true_second :
    (circlePunctureIntersectionRepresentative true).1.1 1 = -1 := by
  rfl

end SphereTopology
end
end
