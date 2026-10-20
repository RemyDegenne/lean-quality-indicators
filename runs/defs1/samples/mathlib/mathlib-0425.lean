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

variable (C)

/-- The constant cosimplicial object. -/
abbrev const : C ⥤ CosimplicialObject C :=
  CategoryTheory.Functor.const _

end CosimplicialObject
end CategoryTheory
end
