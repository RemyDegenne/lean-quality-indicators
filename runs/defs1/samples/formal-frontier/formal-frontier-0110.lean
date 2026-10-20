@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

variable {E B Z : Scheme.{u}} (π : E ⟶ B) (hπ : IsClosedMap π)

/-- The base open consisting of the points whose whole `π`-fibre lies in `W`. -/
def kernImage (W : E.Opens) : B.Opens :=
  ⟨Set.kernImage π W, (isClosedMap_iff_kernImage.mp hπ) W.isOpen⟩

end AlgebraicGeometry.Scheme.Hom
end
