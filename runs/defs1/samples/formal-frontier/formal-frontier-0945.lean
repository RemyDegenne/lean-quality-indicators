public section

open CategoryTheory Limits

open CategoryTheory.MonoidalCategory CartesianMonoidalCategory MonObj

open scoped CategoryTheory.MonObj

noncomputable section

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {G : Scheme.{u}}

/-- A scheme isomorphism restricts to a homeomorphism of closed-point
subspaces, using Mathlib's `schemeIsoToHomeo`. -/
def closedPointsHomeomorphOfIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    closedPoints X ≃ₜ closedPoints Y :=
  e.schemeIsoToHomeo.subtype fun x ↦ by
    simpa using (e.schemeIsoToHomeo.isClosed_image (s := {x})).symm

end AlgebraicGeometry
end
end
