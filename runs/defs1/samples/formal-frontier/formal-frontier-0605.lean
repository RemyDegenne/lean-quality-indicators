@[expose] public section

universe v u

namespace CategoryTheory

open Limits

namespace AdmissibleLayer

variable {C : Type u} [Category.{v} C] [Abelian C] {B : C} {P : ObjectProperty C}

/-- Forget the lower-endpoint bound, retaining the underlying layer. -/
def lowerInclusion (D : Subobject B) : LowerBounded P B D → AdmissibleLayer P B :=
  Subtype.val

end AdmissibleLayer
end CategoryTheory
end
