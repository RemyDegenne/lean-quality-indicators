@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace TopCat

variable {X Y Z : TopCat.{u}}

/-- A homotopy between morphisms in `TopCat` is a homotopy between
the corresponding continuous maps. -/
abbrev Homotopy (f g : X ⟶ Y) := ContinuousMap.Homotopy f.hom g.hom

end TopCat
end
