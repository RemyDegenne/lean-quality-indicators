set_option warningAsError true

set_option backward.isDefEq.respectTransparency false

@[expose] public section

namespace AlgebraicGeometry.RingedSpace.ClosedPointHom

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R] (X : RingedSpace.{u})

/-- The actual map on global sections of any morphism to the affine spectrum. -/
noncomputable def globalSectionsMap (f : X ⟶ Spec.sheafedSpaceObj (CommRingCat.of R)) :
    CommRingCat.of R ⟶ X.presheaf.obj (op ⊤) :=
  (StructureSheaf.globalSectionsIso (CommRingCat.of R)).hom ≫
    f.hom.c.app (op ⊤)

end AlgebraicGeometry.RingedSpace.ClosedPointHom
end
