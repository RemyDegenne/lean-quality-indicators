@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory UnitriangularStageCoordinateRing

open scoped Classical

namespace AlgebraicGeometry

variable (K : Type) [CommRing K] (n r : ℕ)

/-- Section of the *actual* positive-stage underlying coordinate arrow;
not a morphism of group schemes. -/
def unitriangularStageCoordinateSectionOver (hr : 1 ≤ r) :
    (∏ᶜ fun _ : Matrix.UnitriangularGroup.superdiagonalIndex n r =>
      additiveGroupScheme K).X ⟶ unitriangularStageUnderlyingScheme K n r :=
  (additiveGroupProductUnderlyingSpecIso K
      (Matrix.UnitriangularGroup.superdiagonalIndex n r)).hom ≫
    stageProductSpecKill K n r hr ≫
      (unitriangularStageUnderlyingSpecIso K n r).inv

end AlgebraicGeometry
end
end
