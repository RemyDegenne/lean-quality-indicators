@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.IsCofiltered Set CategoryTheory.FunctorToTypes

namespace CategoryTheory

namespace Functor

variable {J : Type u} [Category* J] (F : J ⥤ Type v) {i j k : J} (s : Set (F.obj i))

variable [IsCofilteredOrEmpty J]

/-- The subfunctor of `F` obtained by restricting to the eventual range at each index. -/
@[simps obj map]
def toEventualRanges : J ⥤ Type v where
  obj j := F.eventualRange j
  map f := ↾((F.eventualRange_mapsTo f).restrict _ _ _)

end Functor
end CategoryTheory
end
