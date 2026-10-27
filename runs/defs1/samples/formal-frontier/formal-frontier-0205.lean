@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

/-- Evaluation of the radial homotopy at its equatorial endpoint. -/
def sphere2PunctureIntersectionRadialAtZero :
    C(sphere2PunctureIntersection, sphere2PunctureIntersection) :=
  sphere2PunctureIntersectionRadialHomotopyMap.comp
    ⟨fun p => (0, p), continuous_const.prodMk continuous_id⟩

end SphereTopology
end
end
