@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

/-- The sign-free identity homeomorphism between the two meet orderings. -/
def circlePunctureIntersectionSwapHomeomorph :
    circlePunctureIntersectionReversed ≃ₜ circlePunctureIntersection :=
  Homeomorph.setCongr (by
    ext p
    simp only [circleEastPunctured, circleWestPunctured]
    exact and_comm)

end SphereTopology
end
end
