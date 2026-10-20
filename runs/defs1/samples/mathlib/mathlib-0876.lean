@[expose] public section

universe u

open CategoryTheory Limits Opposite TypeCat

open scoped Simplicial

namespace SSet

variable {X Y Z : SSet.{u}}

/-- The functor which sends a simplicial set to the type of its connected components. -/
@[simps]
def π₀Functor : SSet.{u} ⥤ Type u where
  obj X := π₀ X
  map f := ↾(mapπ₀ f)

end SSet
end
