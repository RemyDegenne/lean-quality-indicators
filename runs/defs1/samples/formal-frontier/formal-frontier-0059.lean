@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

/-- Inclusion of the equator subtype into the twice-punctured sphere. -/
def sphere2EquatorToPunctureIntersection :
    C(sphere2Equator, sphere2PunctureIntersection) :=
  ⟨sphere2EquatorToPunctureIntersectionPoint,
    continuous_sphere2EquatorToPunctureIntersectionPoint⟩

end SphereTopology
end
end
