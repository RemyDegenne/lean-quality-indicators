set_option warningAsError true

set_option backward.isDefEq.respectTransparency false

@[expose] public section

namespace AlgebraicGeometry.RingedSpace.ClosedPointHom

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R] (X : RingedSpace.{u})

/-- The constant map to the unique closed point of a local affine spectrum. -/
def base : (X : TopCat) ⟶ (Spec.sheafedSpaceObj (CommRingCat.of R) : TopCat) :=
  TopCat.ofHom ⟨fun _ => IsLocalRing.closedPoint R, continuous_const⟩

end AlgebraicGeometry.RingedSpace.ClosedPointHom
end
