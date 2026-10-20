@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Category CategoryTheory.Functor TopCat TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

variable (Y : RingedSpace.{u, u}) {T : TopCat.{u}} (g : T ⟶ Y.carrier)

@[simp]
theorem inverseImage_sheaf : (inverseImage Y g).sheaf =
    (TopCat.Sheaf.pullback CommRingCat.{u} g).obj Y.sheaf := rfl

end AlgebraicGeometry.RingedSpace
end
end
