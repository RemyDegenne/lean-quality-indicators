@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Category CategoryTheory.Functor TopCat TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

variable (Y : RingedSpace.{u, u}) {T : TopCat.{u}} (g : T ⟶ Y.carrier)

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The full map from `X` to the inverse-image ringed space, over the identity of `X`. -/
def toInverseImage : X ⟶ inverseImage Y f.hom.base :=
  InducedCategory.homMk
    { base := 𝟙 (X : TopCat)
      c := (inverseImageMap f).hom ≫
        eqToHom (TopCat.Presheaf.Pushforward.id_eq X.presheaf).symm }

end AlgebraicGeometry.RingedSpace
end
end
