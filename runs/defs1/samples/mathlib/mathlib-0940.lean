@[expose] public section

open Opposite

open CategoryTheory

open CategoryTheory.Limits CategoryTheory.Functor

universe v u v' u'

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

namespace CosimplicialObject

scoped[Simplicial]
  notation3:1000 X " ^⦋" n "⦌" =>
    (X : CategoryTheory.CosimplicialObject _).obj (SimplexCategory.mk n)

variable {C}

variable (X : CosimplicialObject C)

open Simplicial

variable (C)

variable {C}

section Truncation

/-- The truncation functor from cosimplicial objects to truncated cosimplicial objects. -/
def truncation (n : ℕ) : CosimplicialObject C ⥤ CosimplicialObject.Truncated C n :=
  (whiskeringLeft _ _ _).obj (SimplexCategory.Truncated.inclusion n)

end Truncation
end CosimplicialObject
end CategoryTheory
end
