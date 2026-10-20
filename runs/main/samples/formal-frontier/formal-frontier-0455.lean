@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

lemma sphere2PunctureIntersectionRadialVector_zero_third
    (p : sphere2PunctureIntersection) :
    sphere2PunctureIntersectionRadialVector 0 p 2 = 0 := by
  simp [sphere2PunctureIntersectionRadialVector,
    sphere2PunctureIntersectionLinearVector_third]

end SphereTopology
end
end
