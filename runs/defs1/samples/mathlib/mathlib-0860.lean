@[expose] public section

namespace CategoryTheory

open Limits

universe v u

variable {C : Type u} [Category.{v} C]

namespace FilteredObject

variable {I : Type*} [Category I]

/-- The forgetful functor `FilteredObject C I ⥤ C`. -/
@[implicit_reducible, simps]
def forget : FilteredObject C I ⥤ C where
  obj A := A.X
  map f := f.hom

end FilteredObject
end CategoryTheory
end
