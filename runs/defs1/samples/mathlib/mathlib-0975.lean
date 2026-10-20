@[expose] public section

universe u w

open CategoryTheory Limits FintypeCat Functor

namespace Profinite

variable {I : Type u} [SmallCategory I] [IsCofiltered I]
    {F : I ⥤ FintypeCat.{max u w}} (c : Cone <| F ⋙ toProfinite)

open Extend

section ProfiniteAsLimit

variable (S : Profinite.{u})

/-- An abbreviation for `S.fintypeDiagram' ⋙ toProfinite`. -/
abbrev diagram' : StructuredArrow S toProfinite ⥤ Profinite :=
  S.fintypeDiagram' ⋙ toProfinite

end ProfiniteAsLimit
end Profinite
end
