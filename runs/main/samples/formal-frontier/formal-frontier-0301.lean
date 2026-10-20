@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

variable {E B Z : Scheme.{u}} (π : E ⟶ B) (hπ : IsClosedMap π)

theorem kernImage_mono : Monotone (π.kernImage hπ) :=
  fun _ _ h ↦ Set.kernImage_mono h

end AlgebraicGeometry.Scheme.Hom
end
