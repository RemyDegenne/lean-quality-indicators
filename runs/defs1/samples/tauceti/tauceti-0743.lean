public section

open CategoryTheory

namespace TauCeti

universe u

namespace DiagonalizableGroup

open AlgebraicGeometry MonObj MonoidalCategory

variable (R : Type u) [CommRing R]

/-- The diagonalizable group scheme `D(G)` bundled as a finite-type affine group scheme. -/
noncomputable def finiteTypeGroupScheme (G : FGCommGrpCat.{u}) :
    FiniteTypeAffineGroupSchemeCat (CommRingCat.of R) :=
  ⟨⟨groupScheme R G, (affineGroupSchemeProperty_iff _).2 inferInstance⟩,
    (finiteTypeAffineGroupSchemeProperty_iff _ _).2
      (locallyOfFiniteType_groupScheme R G)⟩

end DiagonalizableGroup
end TauCeti
end
