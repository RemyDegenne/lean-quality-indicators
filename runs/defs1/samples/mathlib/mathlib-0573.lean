@[expose] public section

universe v u

namespace CategoryTheory

open Bicategory CategoryTheory.Functor

namespace Cat

section

/--
The type of 1-morphisms in the bicategory of categories `Cat`.
This is a structure around `Functor` to prevent defeq-abuse
-/
@[ext]
structure Hom (C D : Cat.{v, u}) where
  ofFunctor ::
  /-- The Functor underlying a 1-morphism in Cat -/
  toFunctor : C ⥤ D

end
end Cat
end CategoryTheory
end
