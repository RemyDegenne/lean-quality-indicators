@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

open Spec (structureSheaf)

attribute [instance] IsAffine.affine

/-- If `f : X ⟶ Y` is a morphism between affine schemes, the corresponding arrow is isomorphic
to the arrow of the morphism on prime spectra induced by the map on global sections. -/
noncomputable
def arrowIsoSpecΓOfIsAffine {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    Arrow.mk f ≅ Arrow.mk (Spec.map f.appTop) :=
  Arrow.isoMk X.isoSpec Y.isoSpec (ΓSpec.adjunction.unit_naturality _)

end AlgebraicGeometry
end
end
