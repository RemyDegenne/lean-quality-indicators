@[expose] public section

noncomputable section

open CategoryTheory AlgebraicTopology

namespace SphereOddDegree

/-- A **sphere-degree setup** bundling the two inputs used by the integral degree theory of sphere
self-maps.

* `orientation : SphereOrientationPos` — a choice of top-homology identification
 `Hₙ(Sⁿ; ℤ) ≅ ℤ` in every dimension `n ≥ 1`, represented by a
 `SphereSuspensionTower`.
* `prism : SingularPrismOperator` — the algebraic prism operator underlying
 homotopy invariance of singular homology.

Bundling both means a downstream consumer assumes **one** hypothesis rather than
several, and every degree theorem — including homotopy invariance — is
unconditional relative to a `SphereDegreeSetup`. The fields are supplied by the final assembly
modules. -/
structure SphereDegreeSetup where
  /-- The positive top-homology orientation `Hₙ(Sⁿ; ℤ) ≅ ℤ` (`n ≥ 1`). -/
  orientation : SphereOrientationPos
  /-- The algebraic prism operator for homotopy invariance of singular homology. -/
  prism : SingularPrismOperator

end SphereOddDegree
end
end
