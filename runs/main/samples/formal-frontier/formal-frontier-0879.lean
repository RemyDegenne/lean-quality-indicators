@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

lemma circlePunctureIntersectionComponent_eq_false_iff
    (p : circlePunctureIntersection) :
    circlePunctureIntersectionComponent p = false ↔ 0 < (p.1.1 : E2) 1 := by
  simp [circlePunctureIntersectionComponent]

end SphereTopology
end
end
