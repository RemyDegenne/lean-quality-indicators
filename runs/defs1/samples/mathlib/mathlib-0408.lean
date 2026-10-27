@[expose] public section

universe u w

open CategoryTheory Limits FintypeCat Functor

namespace Profinite

variable {I : Type u} [SmallCategory I] [IsCofiltered I]
    {F : I ⥤ FintypeCat.{max u w}} (c : Cone <| F ⋙ toProfinite)

open Extend

section ProfiniteAsLimit

variable (S : Profinite.{u})

/--
A functor `StructuredArrow S toProfinite ⥤ FintypeCat` whose limit in `Profinite` is isomorphic
to `S`.
-/
abbrev fintypeDiagram' : StructuredArrow S toProfinite ⥤ FintypeCat :=
  StructuredArrow.proj S toProfinite

end ProfiniteAsLimit
end Profinite
end
