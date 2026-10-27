@[expose] public section

open CategoryTheory TopCat TopologicalSpace Opposite CategoryTheory.Limits CategoryTheory.Category
  CategoryTheory.Functor Topology

universe u v w' w

variable (C : Type u) [Category.{v} C]

namespace AlgebraicGeometry

variable {C}

namespace SheafedSpace

/-- The functor `forgetToPresheafedSpace : SheafedSpace C ⥤ PresheafedSpace C`
is fully faithful. -/
def fullyFaithfulForgetToPresheafedSpace :
    (forgetToPresheafedSpace (C := C)).FullyFaithful where
  preimage f := InducedCategory.homMk f

end SheafedSpace
end AlgebraicGeometry
end
