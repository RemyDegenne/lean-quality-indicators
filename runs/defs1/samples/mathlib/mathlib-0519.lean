@[expose] public section

namespace CategoryTheory

open Bicategory

section

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

/--
A functor between two categories `C` and `D` can be lifted to an oplax functor between the
corresponding locally discrete bicategories.

This is just an abbreviation of `Functor.toPseudofunctor.toOplax`.
-/
@[simps! -isSimp map]
abbrev Functor.toOplaxFunctor : LocallyDiscrete C ⥤ᵒᵖᴸ (LocallyDiscrete D) :=
  F.toPseudofunctor.toOplax

end
end CategoryTheory
end
