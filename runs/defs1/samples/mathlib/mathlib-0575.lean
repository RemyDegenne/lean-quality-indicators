@[expose] public section

universe v u

noncomputable section

open CategoryTheory Limits ConcreteCategory

open CategoryTheory.IsFiltered renaming max → max'

namespace ModuleCat.FilteredColimits

section

variable {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]

variable (F : J ⥤ ModuleCat.{max v u, u} R)

/-- The cocone over the proposed colimit module. -/
@[implicit_reducible]
def colimitCocone : Cocone F where
  pt := colimit F
  ι :=
    { app := coconeMorphism F
      naturality _ _ f := by
        ext
        simpa using! (Types.TypeMax.colimitCocone
          (F ⋙ forget (ModuleCat R))).ι.naturality_apply f _ }

end
end ModuleCat.FilteredColimits
end
end
